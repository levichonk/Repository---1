from pathlib import Path
import runpy
import PIL.Image

# acquire.py only uses PIL.Image.__module__ for a preflight log field.
# Pillow exposes its version on PIL, not this module attribute; provide the
# harmless display value without altering acquisition or validation behavior.
if not hasattr(PIL.Image, "__module__"):
    PIL.Image.__module__ = "PIL.Image"

runpy.run_path(str(Path(__file__).with_name("acquire.py")), run_name="__main__")
