from __future__ import annotations

import concurrent.futures
import csv
import hashlib
import html as html_lib
import io
import json
import os
import re
import shutil
import sys
import time
import unicodedata
import urllib.parse
import zipfile
from datetime import datetime, timezone
from html.parser import HTMLParser
from pathlib import Path

import fitz
import httpx
from PIL import Image

SOURCE_ID = "24453"
SOURCE_URL = "https://media.digitalarkivet.no/view/24453/2"
BASE = "https://media.digitalarkivet.no"
EXPECTED_SCANS = 577
SKILL = {"name": "digitalarkivet-archival-acquisition", "version": "0.1.2-phase5"}
TITLE = "Lister sorenskriveri - Skifteprotokoll nr. 21 med register, 1729-1731"
ARCHIVE_REF = "AV/SAK-1221-0003/H/Hc/L0021"
UA = "digitalarkivet-archival-acquisition/0.1.2-phase5 github-runner"
FIXED_ZIP_TIME = (1980, 1, 1, 0, 0, 0)

ROOT = Path(os.environ.get("RUNNER_TEMP", "/tmp")) / "da24453"
WORK = ROOT / "work"
IMAGES = WORK / "images"
OUTPUT = Path(os.environ.get("GITHUB_WORKSPACE", ".")) / "output"
for p in (ROOT, WORK, IMAGES, OUTPUT):
    p.mkdir(parents=True, exist_ok=True)


def now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def canonical(obj) -> bytes:
    return json.dumps(obj, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")


def atomic_json(path: Path, obj) -> None:
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(obj, ensure_ascii=False, indent=2, sort_keys=True), "utf-8")
    os.replace(tmp, path)


def sha_file(path: Path, chunk: int = 1024 * 1024) -> tuple[str, int]:
    h = hashlib.sha256()
    n = 0
    with path.open("rb") as f:
        while True:
            b = f.read(chunk)
            if not b:
                break
            h.update(b)
            n += len(b)
    return h.hexdigest(), n


def log(stage: str, **kw) -> None:
    rec = {"time": now(), "stage": stage, **kw}
    print(json.dumps(rec, ensure_ascii=False), flush=True)


def get_retry(client: httpx.Client, url: str, accept: str, tries: int = 8) -> httpx.Response:
    last = None
    for attempt in range(tries):
        try:
            r = client.get(url, headers={"Accept": accept})
            if r.status_code in {408, 425, 429, 500, 502, 503, 504}:
                ra = r.headers.get("retry-after")
                delay = float(ra) if ra and ra.isdigit() else min(30.0, 0.75 * (2 ** attempt))
                time.sleep(delay)
                continue
            r.raise_for_status()
            return r
        except Exception as e:
            last = e
            if attempt == tries - 1:
                break
            time.sleep(min(30.0, 0.75 * (2 ** attempt)))
    raise RuntimeError(f"GET failed after retries: {url}: {last}")


class IdAndCandidateParser(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.by_id: dict[str, dict[str, str]] = {}
        self.candidates: list[tuple[str, str, int, str | None, str]] = []
        self.title_depth = 0
        self.title_parts: list[str] = []

    def handle_starttag(self, tag, attrs):
        a = {k.lower(): (v or "") for k, v in attrs}
        if a.get("id"):
            self.by_id.setdefault(a["id"], a)
        if tag == "h1" and a.get("id") == "pageTitle":
            self.title_depth = 1
        elif self.title_depth:
            self.title_depth += 1

        classes = set(a.get("class", "").split())
        explicit = {
            "data-original": ("original", 500, "original", "Original image URL"),
            "data-original-src": ("original", 500, "original", "Original image URL"),
            "data-full": ("full", 475, "full", "Full-size image URL"),
            "data-full-src": ("full", 475, "full", "Full-size image URL"),
            "data-fullsize": ("full", 475, "full", "Full-size image URL"),
            "data-fullsize-src": ("full", 475, "full", "Full-size image URL"),
            "data-hires": ("full", 470, "full", "High-resolution image URL"),
            "data-hires-src": ("full", 470, "full", "High-resolution image URL"),
            "data-highres": ("full", 470, "full", "High-resolution image URL"),
            "data-highres-src": ("full", 470, "full", "High-resolution image URL"),
            "data-iiif-image": ("iiif-full", 460, "iiif-full", "IIIF full image URL"),
            "data-iiif-full": ("iiif-full", 460, "iiif-full", "IIIF full image URL"),
        }
        for key, (kind, pri, quality, label) in explicit.items():
            if a.get(key):
                self.candidates.append((a[key], kind, pri, quality, label))

        if tag == "img":
            if a.get("src") and "viewer-img-zoomable" in classes:
                self.candidates.append((a["src"], "viewer", 300, None, "Viewer image URL"))
            if a.get("srcset"):
                for item in a["srcset"].split(","):
                    bits = item.strip().split()
                    if bits:
                        score = 0
                        if len(bits) > 1 and len(bits[1]) > 1 and bits[1][:-1].isdigit():
                            mult = 1000 if bits[1][-1].lower() == "x" else 1
                            score = int(bits[1][:-1]) * mult
                        self.candidates.append((bits[0], "viewer", 320 + min(score, 100000) // 1000, None, "Viewer srcset image URL"))
        if tag == "source" and a.get("srcset"):
            for item in a["srcset"].split(","):
                bits = item.strip().split()
                if bits:
                    self.candidates.append((bits[0], "viewer", 315, None, "Source srcset image URL"))
        if tag == "meta":
            key = (a.get("property") or a.get("name") or "").lower()
            if key in {"og:image", "og:image:secure_url", "twitter:image", "twitter:image:src"} and a.get("content"):
                self.candidates.append((a["content"], "metadata", 350, None, f"{key} image URL"))
        if tag == "link" and a.get("href"):
            rel = set(a.get("rel", "").lower().split())
            av = a.get("as", "").lower()
            typ = a.get("type", "").lower()
            if "image_src" in rel or ("preload" in rel and av == "image") or typ.startswith("image/"):
                self.candidates.append((a["href"], "metadata", 345, None, "Linked image metadata URL"))
        if tag == "a" and a.get("href") and "download" in a:
            self.candidates.append((a["href"], "download", 390, None, "Viewer download link"))

    def handle_data(self, data):
        if self.title_depth:
            self.title_parts.append(data)

    def handle_endtag(self, tag):
        if self.title_depth:
            self.title_depth -= 1


class OriginalIdParser(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.stack = []
        self.values: dict[str, list[str]] = {}

    def handle_starttag(self, tag, attrs):
        a = {k.lower(): (v or "") for k, v in attrs}
        self.stack.append([tag, a.get("data-originalid"), []])

    def handle_data(self, data):
        for row in self.stack:
            if row[1]:
                row[2].append(data)

    def handle_endtag(self, tag):
        for i in range(len(self.stack) - 1, -1, -1):
            st, key, parts = self.stack[i]
            if st == tag:
                self.stack = self.stack[:i]
                if key:
                    text = " ".join("".join(parts).split())
                    if text and text not in self.values.setdefault(key, []):
                        self.values[key].append(text)
                return


class ContentsParser(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.in_tr = False
        self.in_td = False
        self.in_a = False
        self.cells = []
        self.current = []
        self.link = None
        self.linktext = []
        self.sections = []

    def _idx(self, href: str | None):
        if not href:
            return None
        try:
            parts = urllib.parse.urlparse(href).path.strip("/").split("/")
            for pos in range(len(parts) - 2):
                if parts[pos] == "view" and parts[pos + 1] == SOURCE_ID and parts[pos + 2].isdigit():
                    return int(parts[pos + 2])
        except Exception:
            pass
        return None

    def handle_starttag(self, tag, attrs):
        a = {k.lower(): (v or "") for k, v in attrs}
        if tag == "tr":
            self.in_tr = True
            self.cells = []
            self.link = None
            self.linktext = []
        elif self.in_tr and tag == "td":
            self.in_td = True
            self.current = []
        elif self.in_tr and tag == "a" and self._idx(a.get("href")) is not None:
            self.in_a = True
            self.link = a.get("href")
            self.linktext = []

    def handle_data(self, data):
        if self.in_td:
            self.current.append(data)
        if self.in_a:
            self.linktext.append(data)

    def handle_endtag(self, tag):
        if tag == "a" and self.in_a:
            self.in_a = False
        elif tag == "td" and self.in_td:
            self.cells.append(" ".join("".join(self.current).split()))
            self.in_td = False
        elif tag == "tr" and self.in_tr:
            self.in_tr = False
            idx = self._idx(self.link)
            if idx is not None:
                nonempty = [c for c in self.cells[:-1] if c] or [c for c in self.cells if c]
                label = max(nonempty, key=len) if nonempty else ""
                if label:
                    self.sections.append({
                        "label": label,
                        "start_image_index": idx,
                        "page_label": " ".join("".join(self.linktext).split()),
                    })


def official_url(raw: str | None) -> str | None:
    if not raw:
        return None
    u = urllib.parse.urljoin(BASE, html_lib.unescape(raw.strip()))
    p = urllib.parse.urlparse(u)
    host = (p.hostname or "").lower().rstrip(".")
    allowed = host == "digitalarkivet.no" or host.endswith(".digitalarkivet.no") or host == "arkivverket.no" or host.endswith(".arkivverket.no")
    if p.scheme != "https" or not allowed:
        return None
    return u


QUALITY = {"original": 500, "full": 450, "iiif-full": 425, "permanent": 400, "download": 390, "metadata": 350, "viewer": 300, "preview": 100, "unknown": 0}


def resolve_scan(client: httpx.Client, i: int) -> dict:
    r = get_retry(client, f"{BASE}/view/{SOURCE_ID}/{i}", "text/html,application/xhtml+xml")
    parser = IdAndCandidateParser()
    parser.feed(r.text)
    page = parser.by_id.get("page_no", {}).get("value", "")
    pid = parser.by_id.get("permanent_image_id", {}).get("value")
    permanent = parser.by_id.get("permanent_image_link", {}).get("value")
    reader = parser.by_id.get("reader_link", {}).get("value")
    if not pid or not permanent:
        raise RuntimeError(f"scan {i}: missing explicit permanent image metadata")

    candidates = []
    seen = set()

    def add(raw, kind, priority, explicit_quality=None, label=None):
        u = official_url(raw)
        if not u or u in seen:
            return
        seen.add(u)
        rec = {"url": u, "kind": kind, "priority": int(priority), "label": label or kind}
        if explicit_quality:
            rec["explicit_quality"] = explicit_quality
        candidates.append(rec)

    add(permanent, "permanent", 400, "permanent", "Permanent image URL")
    for raw, kind, pri, quality, label in parser.candidates:
        add(raw, kind, pri, quality, label)
    if not candidates:
        raise RuntimeError(f"scan {i}: no official representation candidate")
    candidates.sort(key=lambda c: (QUALITY.get(c.get("explicit_quality") or c["kind"], 0), c["priority"]), reverse=True)
    chosen = candidates[0]
    explicit_hi = [c for c in candidates if (c.get("explicit_quality") or c["kind"]) in {"original", "full", "iiif-full"}]
    reason = f"Selected {chosen['label']} ({chosen['kind']}) as the highest-ranked official representation discovered through supported explicit viewer metadata."
    if chosen["kind"] == "permanent" and not explicit_hi:
        reason += " No explicit original/full or IIIF-full candidate was exposed; the canonical permanent image URL is selected conservatively."
    return {
        "image_index": i,
        "page_label": page,
        "permanent_image_id": pid,
        "permanent_image_url": official_url(permanent),
        "reader_url": reader,
        "representation_candidates": candidates,
        "representation_discovery": {
            "policy": "supported-official-metadata-v2",
            "candidate_count": len(candidates),
            "explicit_high_fidelity_candidate_found": bool(explicit_hi),
            "explicit_high_fidelity_candidate_urls": [c["url"] for c in explicit_hi],
            "completeness_claim": "best representation discovered through supported explicit viewer metadata; no undisclosed endpoint is assumed absent",
        },
        "selected_representation": chosen,
        "selection_reason": reason,
    }


def validate_image(path: Path, content_type: str | None, expected_length: int | None) -> dict:
    size = path.stat().st_size
    if size <= 0:
        raise RuntimeError(f"empty payload: {path.name}")
    if expected_length is not None and size != expected_length:
        raise RuntimeError(f"Content-Length mismatch: {path.name}: {size} != {expected_length}")
    with path.open("rb") as f:
        magic = f.read(16)
    if not magic.startswith(b"\xff\xd8\xff"):
        raise RuntimeError(f"non-JPEG payload: {path.name}")
    ct = (content_type or "").split(";", 1)[0].lower().strip()
    if ct and ct not in {"image/jpeg", "application/octet-stream"}:
        raise RuntimeError(f"unexpected media type {ct}: {path.name}")
    with Image.open(path) as im:
        width, height = im.size
        mode = im.mode
        fmt = im.format
        im.verify()
    if fmt != "JPEG" or width <= 0 or height <= 0:
        raise RuntimeError(f"decoder verification failed: {path.name}")
    digest, n = sha_file(path)
    return {"media_type": ct or "image/jpeg", "detected_format": "jpeg", "width": width, "height": height, "mode": mode, "byte_count": n, "sha256": digest}


def acquire_scan(client: httpx.Client, row: dict) -> dict:
    idx = row["image_index"]
    safe_pid = re.sub(r"[^A-Za-z0-9_.-]+", "_", row["permanent_image_id"])
    final = IMAGES / f"scan-{idx:03d}_{safe_pid}.jpg"
    part = Path(str(final) + ".part")
    last = None
    for attempt in range(8):
        try:
            with client.stream("GET", row["selected_representation"]["url"], headers={"Accept": "image/*,*/*;q=0.1"}) as r:
                if r.status_code in {408, 425, 429, 500, 502, 503, 504}:
                    ra = r.headers.get("retry-after")
                    delay = float(ra) if ra and ra.isdigit() else min(30.0, 0.75 * (2 ** attempt))
                    time.sleep(delay)
                    continue
                r.raise_for_status()
                ctype = r.headers.get("content-type")
                cl = r.headers.get("content-length")
                expected = int(cl) if cl and cl.isdigit() else None
                with part.open("wb") as f:
                    for chunk in r.iter_bytes(1024 * 1024):
                        f.write(chunk)
            validation = validate_image(part, ctype, expected)
            os.replace(part, final)
            return {
                "image_index": idx,
                "page_label": row["page_label"],
                "permanent_image_id": row["permanent_image_id"],
                "permanent_image_url": row["permanent_image_url"],
                "selected_representation": row["selected_representation"],
                "selection_reason": row["selection_reason"],
                "local_filename": final.name,
                "local_path": str(final),
                "validation": validation,
                "status": "complete",
            }
        except Exception as e:
            last = e
            part.unlink(missing_ok=True)
            if attempt < 7:
                time.sleep(min(30.0, 0.75 * (2 ** attempt)))
    raise RuntimeError(f"scan {idx} acquisition failed: {last}")


def sanitize(text: str, limit: int = 190) -> str:
    text = unicodedata.normalize("NFC", str(text)).replace("/", "_")
    bad = set('<>:"/\\|?*')
    text = "".join("_" if c in bad or ord(c) < 32 else c for c in text)
    text = " ".join(text.split()).strip(" .") or "unnamed"
    if len(text) > limit:
        suffix = hashlib.sha256(text.encode()).hexdigest()[:8]
        text = text[: limit - 9].rstrip() + "-" + suffix
    return text


def package_name(row: dict) -> str:
    label = row.get("page_label") or "upaginert"
    return sanitize(f"Lister sorenskriveri, {ARCHIVE_REF.replace('/', '_')} - Skifteprotokoll nr. 21, 1729-1731, bilde {row['image_index']:03d}, s. {label}.jpg")


def zip_write_bytes(z: zipfile.ZipFile, arcname: str, data: bytes):
    zi = zipfile.ZipInfo(arcname, FIXED_ZIP_TIME)
    zi.compress_type = zipfile.ZIP_STORED
    zi.external_attr = 0o100644 << 16
    z.writestr(zi, data)


def zip_write_file(z: zipfile.ZipFile, arcname: str, path: Path):
    zi = zipfile.ZipInfo(arcname, FIXED_ZIP_TIME)
    zi.compress_type = zipfile.ZIP_STORED
    zi.external_attr = 0o100644 << 16
    zi.file_size = path.stat().st_size
    with path.open("rb") as src, z.open(zi, "w", force_zip64=True) as dst:
        shutil.copyfileobj(src, dst, length=1024 * 1024)


def pdf_escape(value: str) -> bytes:
    return str(value).replace("\\", "\\\\").replace("(", "\\(").replace(")", "\\)").encode("latin-1", "replace")


def build_pdf(scans: list[dict], pdf_path: Path, sections: list[dict]) -> dict:
    n_pages = len(scans)
    page_obj = [6 + 3 * i for i in range(n_pages)]
    image_obj = [7 + 3 * i for i in range(n_pages)]
    content_obj = [8 + 3 * i for i in range(n_pages)]
    useful_sections = [s for s in sections if 1 <= s["start_image_index"] <= n_pages]
    outline_start = 6 + 3 * n_pages
    outline_obj = list(range(outline_start, outline_start + len(useful_sections)))
    max_obj = outline_obj[-1] if outline_obj else 5 + 3 * n_pages
    offsets = [0] * (max_obj + 1)

    def write_obj(f, num: int, body: bytes):
        offsets[num] = f.tell()
        f.write(f"{num} 0 obj\n".encode())
        f.write(body)
        f.write(b"\nendobj\n")

    with pdf_path.open("wb") as f:
        f.write(b"%PDF-1.7\n%\xe2\xe3\xcf\xd3\n")
        catalog = b"<< /Type /Catalog /Pages 2 0 R /PageLabels 4 0 R /Outlines 5 0 R /PageMode /UseOutlines >>"
        write_obj(f, 1, catalog)
        kids = " ".join(f"{x} 0 R" for x in page_obj)
        write_obj(f, 2, f"<< /Type /Pages /Count {n_pages} /Kids [{kids}] >>".encode())
        info = b"<< /Title (" + pdf_escape(TITLE) + b") /Subject (Digitalarkivet source 24453 archival image derivative) /Creator (digitalarkivet-archival-acquisition 0.1.2-phase5) >>"
        write_obj(f, 3, info)
        nums = []
        for i, row in enumerate(scans):
            nums.append(str(i).encode() + b" << /P (" + pdf_escape(row.get("page_label") or str(row["image_index"])) + b") >>")
        write_obj(f, 4, b"<< /Nums [" + b" ".join(nums) + b"] >>")
        if outline_obj:
            write_obj(f, 5, f"<< /Type /Outlines /First {outline_obj[0]} 0 R /Last {outline_obj[-1]} 0 R /Count {len(outline_obj)} >>".encode())
        else:
            write_obj(f, 5, b"<< /Type /Outlines /Count 0 >>")

        for i, row in enumerate(scans):
            width = row["validation"]["width"]
            height = row["validation"]["height"]
            wp = width * 72.0 / 300.0
            hp = height * 72.0 / 300.0
            mode = row["validation"]["mode"]
            colorspace = "/DeviceGray" if mode == "L" else "/DeviceCMYK" if mode == "CMYK" else "/DeviceRGB"
            page_body = f"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 {wp:.6f} {hp:.6f}] /Resources << /XObject << /Im0 {image_obj[i]} 0 R >> >> /Contents {content_obj[i]} 0 R >>".encode()
            write_obj(f, page_obj[i], page_body)

            image_path = Path(row["local_path"])
            img_len = image_path.stat().st_size
            decode = " /Decode [1 0 1 0 1 0 1 0]" if mode == "CMYK" else ""
            offsets[image_obj[i]] = f.tell()
            f.write(f"{image_obj[i]} 0 obj\n".encode())
            f.write(f"<< /Type /XObject /Subtype /Image /Width {width} /Height {height} /ColorSpace {colorspace} /BitsPerComponent 8 /Filter /DCTDecode{decode} /Length {img_len} >>\nstream\n".encode())
            with image_path.open("rb") as src:
                shutil.copyfileobj(src, f, length=1024 * 1024)
            f.write(b"\nendstream\nendobj\n")

            content = f"q {wp:.6f} 0 0 {hp:.6f} 0 0 cm /Im0 Do Q\n".encode()
            offsets[content_obj[i]] = f.tell()
            f.write(f"{content_obj[i]} 0 obj\n<< /Length {len(content)} >>\nstream\n".encode())
            f.write(content)
            f.write(b"endstream\nendobj\n")

        for j, section in enumerate(useful_sections):
            num = outline_obj[j]
            parts = [
                b"/Title (" + pdf_escape(section["label"]) + b")",
                b"/Parent 5 0 R",
                f"/Dest [{page_obj[section['start_image_index'] - 1]} 0 R /Fit]".encode(),
            ]
            if j > 0:
                parts.append(f"/Prev {outline_obj[j - 1]} 0 R".encode())
            if j + 1 < len(outline_obj):
                parts.append(f"/Next {outline_obj[j + 1]} 0 R".encode())
            write_obj(f, num, b"<< " + b" ".join(parts) + b" >>")

        xref = f.tell()
        f.write(f"xref\n0 {max_obj + 1}\n".encode())
        f.write(b"0000000000 65535 f \n")
        for num in range(1, max_obj + 1):
            f.write(f"{offsets[num]:010d} 00000 n \n".encode())
        f.write(f"trailer\n<< /Size {max_obj + 1} /Root 1 0 R /Info 3 0 R >>\nstartxref\n{xref}\n%%EOF\n".encode())

    doc = fitz.open(pdf_path)
    if doc.page_count != n_pages:
        raise RuntimeError(f"PDF page-count mismatch: {doc.page_count} != {n_pages}")
    raw_verified = 0
    label_verified = 0
    for i, row in enumerate(scans):
        images = doc[i].get_images(full=True)
        if len(images) != 1:
            raise RuntimeError(f"PDF page {i+1}: expected 1 image, found {len(images)}")
        raw = doc.xref_stream_raw(images[0][0])
        if hashlib.sha256(raw).hexdigest() != row["validation"]["sha256"]:
            raise RuntimeError(f"PDF page {i+1}: raw JPEG SHA-256 mismatch")
        raw_verified += 1
        expected_label = row.get("page_label") or str(row["image_index"])
        if doc[i].get_label() != expected_label:
            raise RuntimeError(f"PDF page {i+1}: label mismatch {doc[i].get_label()!r} != {expected_label!r}")
        label_verified += 1
    toc = doc.get_toc(simple=True)
    samples = []
    for idx in sorted({0, n_pages // 2, n_pages - 1}):
        pix = doc[idx].get_pixmap(matrix=fitz.Matrix(0.35, 0.35), alpha=False)
        sample_path = OUTPUT / f"render-sample-{idx+1:03d}.png"
        pix.save(sample_path)
        sample_sha, sample_bytes = sha_file(sample_path)
        samples.append({"page": idx + 1, "sha256": sample_sha, "bytes": sample_bytes, "width": pix.width, "height": pix.height})
    doc.close()
    digest, size = sha_file(pdf_path)
    return {
        "status": "VERIFIED",
        "page_count": n_pages,
        "raw_dct_streams_verified": raw_verified,
        "logical_page_labels_verified": label_verified,
        "toc_entries": len(toc),
        "pdf_sha256": digest,
        "pdf_bytes": size,
        "render_samples": samples,
        "verified_at_utc": now(),
    }


def main():
    log("preflight", python=sys.version.split()[0], httpx=httpx.__version__, pillow=Image.__module__, pymupdf=fitz.VersionBind)
    timeout = httpx.Timeout(180.0, connect=30.0, read=180.0, write=180.0, pool=30.0)
    limits = httpx.Limits(max_connections=24, max_keepalive_connections=16)
    with httpx.Client(follow_redirects=True, timeout=timeout, limits=limits, headers={"User-Agent": UA}) as client:
        first = get_retry(client, f"{BASE}/view/{SOURCE_ID}/1", "text/html,application/xhtml+xml").text
        contents = get_retry(client, f"{BASE}/sk/contents/{SOURCE_ID}", "text/html,application/xhtml+xml").text
        p0 = IdAndCandidateParser()
        p0.feed(first)
        count_raw = p0.by_id.get("image_no", {}).get("max") or p0.by_id.get("nav-slider", {}).get("data-max")
        if not count_raw or not str(count_raw).isdigit():
            raise RuntimeError("unable to determine advertised scan count")
        scan_count = int(count_raw)
        if scan_count != EXPECTED_SCANS:
            raise RuntimeError(f"source scan count changed: {scan_count} != {EXPECTED_SCANS}")

        op = OriginalIdParser()
        op.feed(contents)
        cp = ContentsParser()
        cp.feed(contents)
        source = {
            "source_id": SOURCE_ID,
            "scan_count": scan_count,
            "canonical_source_url": f"{BASE}/view/{SOURCE_ID}/1",
            "contents_url": f"{BASE}/sk/contents/{SOURCE_ID}",
            "title": TITLE,
            "archive_reference": (op.values.get("archives-ref") or [ARCHIVE_REF])[0],
            "archive": op.values.get("archive", []),
            "series": op.values.get("series", []),
            "folder": op.values.get("folder", []),
            "source_type": op.values.get("sourcetype", []),
            "period": op.values.get("period", []),
            "area": op.values.get("area", []),
            "notes": op.values.get("notes", []),
        }

        log("resolving", expected=scan_count)
        with concurrent.futures.ThreadPoolExecutor(max_workers=12) as ex:
            rows = list(ex.map(lambda i: resolve_scan(client, i), range(1, scan_count + 1)))
        rows.sort(key=lambda r: r["image_index"])
        if [r["image_index"] for r in rows] != list(range(1, scan_count + 1)):
            raise RuntimeError("source-map ordering/completeness invariant failed")
        scope = {"kind": "all", "requested_scan_count": scan_count, "first_image_index": 1, "last_image_index": scan_count}
        map_core = {"source": source, "scope": scope, "sections": cp.sections, "scans": rows}
        map_fp = hashlib.sha256(canonical(map_core)).hexdigest()
        source_map = {"source_map_schema_version": "1.0", "resolved_at_utc": now(), **map_core, "map_fingerprint_sha256": map_fp}
        atomic_json(WORK / "source-map.json", source_map)

        request = {
            "job_schema_version": "1.0",
            "source": {"input": SOURCE_URL, "source_id": SOURCE_ID},
            "scope": {"kind": "all"},
            "quality": {"profile": "archival-max", "allow_degraded_fallback": False},
            "outputs": {"zip": True, "pdf": True, "manifest_json": True, "manifest_csv": True, "checksums_sha256": True},
            "naming": {"profile": "archival-descriptive-v1"},
            "delivery": {"mode": "auto", "preferred": "google-drive", "temporary_fallback": True, "temporary_fallback_public_only": True},
            "resume": True,
        }
        atomic_json(WORK / "request.json", request)

        log("acquiring", expected=scan_count)
        acquired = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex:
            futures = [ex.submit(acquire_scan, client, row) for row in rows]
            for k, fut in enumerate(concurrent.futures.as_completed(futures), 1):
                acquired.append(fut.result())
                if k % 25 == 0 or k == scan_count:
                    log("acquiring", completed=k, expected=scan_count)
        acquired.sort(key=lambda r: r["image_index"])

    if len(acquired) != scan_count or any(r["status"] != "complete" for r in acquired):
        raise RuntimeError("acquisition completeness invariant failed")
    total_source_bytes = sum(r["validation"]["byte_count"] for r in acquired)
    state = {
        "schema_version": "1.0",
        "status": "COMPLETE",
        "source_map_fingerprint_sha256": map_fp,
        "finished_at": now(),
        "summary": {"requested": scan_count, "resolved": scan_count, "acquired": scan_count, "validated": scan_count, "total_source_bytes": total_source_bytes},
        "scans": {str(r["image_index"]): r for r in acquired},
    }
    atomic_json(WORK / "acquisition-state.json", state)
    log("acquired", count=scan_count, total_source_bytes=total_source_bytes)

    content_set_fp = hashlib.sha256(canonical([
        {"image_index": r["image_index"], "permanent_image_id": r["permanent_image_id"], "sha256": r["validation"]["sha256"]}
        for r in acquired
    ])).hexdigest()
    job_fp = hashlib.sha256(canonical(request)).hexdigest()
    acquisition_id = f"DA-{SOURCE_ID}-all-{datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')}-{job_fp[:8]}"
    root_name = "Lister_sorenskriveri_L0021_Skifteprotokoll_nr_21_1729-1731"

    manifest_scans = []
    for srcrow, got in zip(rows, acquired):
        manifest_scans.append({
            "image_index": got["image_index"],
            "page_label": got["page_label"],
            "permanent_image_id": got["permanent_image_id"],
            "permanent_image_url": got["permanent_image_url"],
            "selected_representation": got["selected_representation"],
            "selection_reason": got["selection_reason"],
            "byte_count": got["validation"]["byte_count"],
            "sha256": got["validation"]["sha256"],
            "width": got["validation"]["width"],
            "height": got["validation"]["height"],
            "mode": got["validation"]["mode"],
            "package_filename": package_name(got),
        })

    manifest = {
        "manifest_schema_version": "1.0",
        "acquisition_id": acquisition_id,
        "created_at_utc": now(),
        "skill": SKILL,
        "request": request,
        "source": source,
        "scope": scope,
        "quality": {"profile": "archival-max", "representation_claim": "best representation discovered through supported explicit Digitalarkivet metadata; no undisclosed endpoint is assumed absent"},
        "source_map_fingerprint_sha256": map_fp,
        "job_fingerprint_sha256": job_fp,
        "content_set_fingerprint_sha256": content_set_fp,
        "access_classification": "PUBLIC",
        "access_evidence": "All requested viewer pages and selected source representations were retrieved without authentication or special authorization during this run.",
        "scans": manifest_scans,
    }

    source_out = OUTPUT / "source.json"
    request_out = OUTPUT / "request.json"
    map_out = OUTPUT / "source-map.json"
    manifest_out = OUTPUT / "manifest.json"
    csv_out = OUTPUT / "manifest.csv"
    report_out = OUTPUT / "acquisition-report.md"
    readme_out = OUTPUT / "README.md"
    sums_out = OUTPUT / "SHA256SUMS.txt"
    atomic_json(source_out, source)
    shutil.copy2(WORK / "request.json", request_out)
    shutil.copy2(WORK / "source-map.json", map_out)
    atomic_json(manifest_out, manifest)

    sio = io.StringIO()
    writer = csv.writer(sio)
    headers = ["image_index", "page_label", "permanent_image_id", "permanent_image_url", "package_filename", "byte_count", "sha256", "width", "height"]
    writer.writerow(headers)
    for r in manifest_scans:
        writer.writerow([r[h] for h in headers])
    csv_out.write_text(sio.getvalue(), "utf-8")

    readme_out.write_text(
        f"# Digitalarkivet archival acquisition\n\nSource: {TITLE}\n\nSource ID: {SOURCE_ID}\nArchive reference: {ARCHIVE_REF}\nScope: all {scan_count} scans\nAcquisition ID: {acquisition_id}\nSkill: {SKILL['name']} {SKILL['version']}\n\nThe images/ directory preserves the exact validated selected JPEG response bytes in Digitalarkivet viewer order. The PDF is a chronological derivative; the ZIP image bytes remain the archival authority.\n",
        "utf-8",
    )
    report_out.write_text(
        f"# Acquisition report\n\n- Terminal acquisition status: COMPLETE\n- Source: {TITLE}\n- Source ID: {SOURCE_ID}\n- Archive reference: {ARCHIVE_REF}\n- Requested/resolved/acquired/validated scans: {scan_count}/{scan_count}/{scan_count}/{scan_count}\n- First/last scan: 1/{scan_count}\n- Quality: archival-max, supported explicit-metadata discovery\n- Total source bytes: {total_source_bytes}\n- Source-map fingerprint SHA-256: {map_fp}\n- Content-set fingerprint SHA-256: {content_set_fp}\n- Access classification: PUBLIC\n- Skill: {SKILL['version']}\n- Acquisition ID: {acquisition_id}\n",
        "utf-8",
    )

    sum_rows = []
    for p in [readme_out, request_out, source_out, map_out, manifest_out, csv_out, report_out]:
        digest, _ = sha_file(p)
        sum_rows.append((digest, p.name))
    for ms, got in zip(manifest_scans, acquired):
        sum_rows.append((got["validation"]["sha256"], "images/" + ms["package_filename"]))
    sums_out.write_text("".join(f"{h}  {name}\n" for h, name in sum_rows), "utf-8")

    log("packaging")
    zip_path = OUTPUT / f"{root_name}_all_{scan_count}_scans.zip"
    expected_members = []
    with zipfile.ZipFile(zip_path, "w", compression=zipfile.ZIP_STORED, allowZip64=True) as z:
        for p in [readme_out, request_out, source_out, map_out, manifest_out, csv_out, report_out, sums_out]:
            arc = f"{root_name}/{p.name}"
            zip_write_file(z, arc, p)
            expected_members.append(arc)
        for ms, got in zip(manifest_scans, acquired):
            arc = f"{root_name}/images/{ms['package_filename']}"
            zip_write_file(z, arc, Path(got["local_path"]))
            expected_members.append(arc)

    with zipfile.ZipFile(zip_path, "r") as z:
        bad = z.testzip()
        if bad:
            raise RuntimeError(f"ZIP CRC failure: {bad}")
        if z.namelist() != expected_members:
            raise RuntimeError("ZIP member/order mismatch")
        for ms in manifest_scans:
            data = z.read(f"{root_name}/images/{ms['package_filename']}")
            if hashlib.sha256(data).hexdigest() != ms["sha256"]:
                raise RuntimeError(f"inside-ZIP image SHA mismatch at scan {ms['image_index']}")
    zip_sha, zip_bytes = sha_file(zip_path)
    package_verification = {
        "status": "VERIFIED",
        "zip_filename": zip_path.name,
        "zip_bytes": zip_bytes,
        "zip_sha256": zip_sha,
        "member_count": len(expected_members),
        "image_count": scan_count,
        "crc_test": "PASS",
        "membership_order": "PASS",
        "inside_zip_image_sha256_count": scan_count,
        "source_byte_equality": "PASS",
        "verified_at_utc": now(),
    }
    atomic_json(OUTPUT / "package-verification.json", package_verification)
    log("package_verified", zip_bytes=zip_bytes, zip_sha256=zip_sha)

    log("pdf_build", pages=scan_count)
    pdf_path = OUTPUT / f"{root_name}_chronological_{scan_count}_pages.pdf"
    pdf_verification = build_pdf(acquired, pdf_path, cp.sections)
    atomic_json(OUTPUT / "pdf-verification.json", pdf_verification)
    if pdf_verification["page_count"] != scan_count or pdf_verification["raw_dct_streams_verified"] != scan_count or pdf_verification["logical_page_labels_verified"] != scan_count:
        raise RuntimeError("PDF verification invariant failed")
    log("pdf_verified", pdf_bytes=pdf_verification["pdf_bytes"], pdf_sha256=pdf_verification["pdf_sha256"])

    summary = {
        "status": "COMPLETE_LOCAL_VERIFIED",
        "skill": SKILL,
        "source_id": SOURCE_ID,
        "source_title": TITLE,
        "archive_reference": ARCHIVE_REF,
        "scan_count": scan_count,
        "acquisition_id": acquisition_id,
        "total_source_bytes": total_source_bytes,
        "source_map_fingerprint_sha256": map_fp,
        "content_set_fingerprint_sha256": content_set_fp,
        "zip": package_verification,
        "pdf": pdf_verification,
        "access_classification": "PUBLIC",
        "created_at_utc": now(),
    }
    atomic_json(OUTPUT / "run-summary.json", summary)
    print("FINAL_SUMMARY=" + json.dumps(summary, ensure_ascii=False, separators=(",", ":")), flush=True)


if __name__ == "__main__":
    main()
