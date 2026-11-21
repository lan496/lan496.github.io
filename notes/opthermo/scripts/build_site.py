"""Assemble the browsable site under site/.

site/index.html          landing page
site/blueprint/          blueprint web version (run scripts/build_figures.py, then `leanblueprint web`)
site/blueprint.pdf       blueprint pdf (run `leanblueprint pdf` first)
site/code.html           README and every Lean source on one page

Usage: python3 scripts/build_site.py
"""

import re
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SOURCES = [
    "OpThermo/Measurement.lean",
    "OpThermo/StateSpace.lean",
    "OpThermo/States.lean",
    "OpThermo/Mechanics.lean",
    "OpThermo/FirstLaw.lean",
    "OpThermo/Entropy.lean",
    "OpThermo/Accessibility.lean",
    "OpThermo/Model.lean",
    "OpThermo/Temperature.lean",
    "OpThermo/Gibbs.lean",
    "OpThermo/Potentials.lean",
    "OpThermo/Concavity.lean",
    "OpThermo/HeatCapacity.lean",
    "AxiomCheck.lean",
]
CSS = """
body { max-width: 60rem; margin: auto; padding: 1rem; line-height: 1.6;
       font-family: -apple-system, "Hiragino Sans", sans-serif; }
pre { background: #f6f8fa; padding: 0.8rem; overflow-x: auto; font-size: 0.85rem;
      line-height: 1.4; }
code { font-family: "SF Mono", Menlo, monospace; }
table { border-collapse: collapse; font-size: 0.9rem; }
th, td { border: 1px solid #ccc; padding: 0.3rem 0.5rem; }
"""


# MathJax 4 with a copy handler: copying a selection puts the TeX source of each formula
# (as $...$ or $$...$$) on the clipboard instead of the rendered glyphs.
MATHJAX = r"""<script>
  MathJax = {
    tex: { inlineMath: [['$','$'], ['\\(','\\)']] },
  };
  // MathJax 4 may re-render formulas after load, so tag the current containers at copy time.
  function tagFormulas() {
    for (const item of MathJax.startup.document.math) {
      const root = item.typesetRoot;
      if (!root) continue;
      root.setAttribute('data-tex', item.math.trim());
      if (item.display) root.setAttribute('data-display', 'true');
    }
  }
  document.addEventListener('copy', (event) => {
    const sel = window.getSelection();
    if (!sel || sel.rangeCount === 0 || !window.MathJax || !MathJax.startup) return;
    tagFormulas();
    const frag = sel.getRangeAt(0).cloneContents();
    const boxes = frag.querySelectorAll('mjx-container[data-tex]');
    if (boxes.length === 0) return;
    for (const box of boxes) {
      const tex = box.getAttribute('data-tex').replace(/\{\\gt\}/g, '>').replace(/\{\\lt\}/g, '<');
      const text = box.hasAttribute('data-display') ? '\n$$' + tex + '$$\n' : '$' + tex + '$';
      box.replaceWith(document.createTextNode(text));
    }
    const holder = document.createElement('div');
    holder.style.position = 'fixed';
    holder.style.left = '-10000px';
    holder.appendChild(frag);
    document.body.appendChild(holder);
    const plain = holder.innerText;
    holder.remove();
    event.clipboardData.setData('text/plain', plain);
    event.preventDefault();
  });
</script>
<script src="https://cdn.jsdelivr.net/npm/mathjax@4/tex-chtml.js"></script>
"""


def upgrade_mathjax(html: str) -> str:
    """Replace plasTeX's MathJax 3 block (config script and loader) with MATHJAX."""
    pattern = re.compile(
        r"<script(?: type=\"text/x-mathjax-config\")?>\s*MathJax.*?"
        r"<script[^>]*mathjax@3/es5/tex-chtml\.js\">\s*</script>\n?",
        re.S,
    )
    return pattern.sub(lambda _: MATHJAX, html, count=1)


INDEX = """<!doctype html>
<html lang="ja"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>OpThermo</title>
<style>body{max-width:60rem;margin:auto;padding:1rem;line-height:1.7;
font-family:-apple-system,"Hiragino Sans",sans-serif}
img{max-width:100%;height:auto}</style></head>
<body>
<h1>OpThermo</h1>
<p>操作主義による熱力学の Lean 4 形式化。</p>
<p><img src="chain.svg" alt="概念の依存関係"></p>
<p>比較と連結の法則から長さ、質量、時間の目盛りを作り、仕事、内部エネルギー、断熱到達性、エントロピー、温度、Gibbs 自由エネルギーへと進む。</p>
<ul>
<li><a href="blueprint/index.html">Blueprint (Web)</a>：定理を数式と日本語で述べ、Lean の宣言と依存グラフに対応づけたもの。まずはこちら。</li>
<li><a href="blueprint/dep_graph_document.html">依存グラフ</a></li>
<li><a href="blueprint.pdf">Blueprint (PDF)</a></li>
<li><a href="code.html">README と Lean ソース全文</a></li>
</ul>
</body></html>
"""


def main():
    parts = [(ROOT / "README.md").read_text()]
    for rel in SOURCES:
        code = (ROOT / rel).read_text()
        parts.append(f"# `{rel}`\n\n````lean\n{code}````\n")
    site = ROOT / "site"
    site.mkdir(exist_ok=True)
    shutil.copytree(ROOT / "blueprint" / "web", site / "blueprint", dirs_exist_ok=True)
    for page in (site / "blueprint").glob("*.html"):
        page.write_text(upgrade_mathjax(page.read_text()))
    shutil.copy(ROOT / "blueprint" / "print" / "print.pdf", site / "blueprint.pdf")
    shutil.copy(ROOT / "blueprint" / "src" / "figures" / "chain.svg", site / "chain.svg")
    (site / "index.html").write_text(INDEX)
    out = site / "code.html"
    with tempfile.TemporaryDirectory() as tmp:
        md = Path(tmp) / "all.md"
        css = Path(tmp) / "style.css"
        md.write_text("\n\n".join(parts))
        css.write_text(CSS)
        subprocess.run(
            ["pandoc", str(md), "-s", "--toc", "--toc-depth=2", "--embed-resources",
             "--css", str(css), "--metadata", "title=OpThermo", "-o", str(out)],
            check=True,
        )
    print(out)


if __name__ == "__main__":
    main()
