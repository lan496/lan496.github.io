---
title: "MathJax test"
use_math: true
---

InlineMath $x_{1}, \dots x_{n}$

DisplayMath need to be wrapped by `<div>`
<div>
$$
\sum_{n=1}^{\infty} \frac{1}{n^{2}} = \frac{\pi^{2}}{6}
$$
</div>

\begin{equation}
  \label{eq:sample}
  e^{\pi i} + 1 = 0
\end{equation}

You can refer numbered equation like Eq. \eqref{eq:sample}.

Refer [some page][markdown_ref]

[markdown_ref]: https://commonmark.org/help/
