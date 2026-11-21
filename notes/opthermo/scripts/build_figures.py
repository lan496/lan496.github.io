"""Compile the TikZ figures of the blueprint to PDF (print) and SVG (web).

Run from the repository root before `leanblueprint web` / `leanblueprint pdf`:

    python3 scripts/build_figures.py
"""

import re
import subprocess
import sys
import tempfile
from pathlib import Path

FIG_DIR = Path(__file__).resolve().parent.parent / "blueprint" / "src" / "figures"
# Web display size relative to print size, so figure text matches the body text on screen.
# CSS caps the width at the column width.
SVG_SCALE = 1.6


def main() -> None:
    sources = sorted(p for p in FIG_DIR.glob("*.tex") if p.stem != "preamble")
    for src in sources:
        build(src)
        print(f"built {src.stem}")


def build(src: Path) -> None:
    with tempfile.TemporaryDirectory() as tmp:
        result = subprocess.run(
            ["xelatex", "-interaction=nonstopmode", "-halt-on-error",
             f"-output-directory={tmp}", src.name],
            cwd=FIG_DIR, capture_output=True, text=True,
        )
        if result.returncode != 0:
            sys.exit(f"xelatex failed on {src.name}:\n{result.stdout[-3000:]}")
        pdf = FIG_DIR / f"{src.stem}.pdf"
        pdf.write_bytes((Path(tmp) / f"{src.stem}.pdf").read_bytes())
    svg = pdf.with_suffix(".svg")
    subprocess.run(["pdftocairo", "-svg", str(pdf), str(svg)], check=True)
    svg.write_text(scale_svg(svg.read_text()))


def scale_svg(text: str) -> str:
    """Enlarge the declared width and height of the root <svg>; its viewBox keeps the drawing."""
    def scale(m: re.Match) -> str:
        return f'{m.group(1)}="{float(m.group(2)) * SVG_SCALE:.2f}pt"'
    root = re.search(r"<svg[^>]*>", text)
    tag = re.sub(r'(width|height)="([0-9.]+)pt"', scale, root.group(0))
    return text[: root.start()] + tag + text[root.end():]


if __name__ == "__main__":
    main()
