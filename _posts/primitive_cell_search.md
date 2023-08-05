---
title: "Primitive cell search problem"
layout: posts
use_math: true
---

## Problem statement

Let $\mathbf{A} = (\mathbf{a}\_{1} \mathbf{a}\_{2} \mathbf{a}\_{3})$ be basis vectors.
Their dual basis vectors are written as $\mathbf{B} = (\mathbf{b}\_{1} \mathbf{b}\_{2} \mathbf{b}\_{3}) = \mathbf{A}^{-\top}$.
Given point coordinates $X = (\mathbf{x}\_{i})\_{i=1}^{N}$ w.r.t. $\mathbf{A}$,
we consider to search for their primitive basis vectors $\mathbf{A}\_{p}\mathbf{M}=\mathbf{A}$:

\begin{equation}
    \mathrm{argmin}\_{ \mathbf{M} \in \mathbb{Z}^{3 \times 3} } \, \det \mathbf{M} \,
    \mathrm{s.t.}
        \forall \mathbf{x}, \mathbf{x}' \in X,
        \mathbf{M}(\mathbf{x} - \mathbf{x}') \in \mathbb{Z}^{3}
\end{equation}

## Naive solution in real space: $O(N^{2})$


Loop over $\mathbf{x}, \mathbf{x}' \in X$ and find pure translations (implemented in [symmetry.c:search_pure_translations](https://github.com/spglib/spglib/blob/71cc0527afe1d64ef81d11fae1908bc4d34fd4b8/src/symmetry.c#L554-L603)).

## Reciprocal space method?

cctbx seems to find pure translations in reciprocal space, c.f. [structure_factor_symmetry](https://github.com/cctbx/cctbx_project/blob/master/cctbx/symmetry_search.py).

When (real) primitive lattice is written as $\mathcal{L} = \mathbf{A}\mathbf{M}^{-1} \mathbb{Z}^{3}$, its dual lattice is written as $\mathcal{L}^{\ast} = \mathbf{B} (\mathbf{B}^{-1} \mathbf{M}^{\top} \mathbf{B}) \mathbb{Z}^{3}$.

The reciprocal lattice will also be characterized by the structure factor:
\begin{equation}
    F(\mathbf{k}) = \left| \sum_{ \mathbf{x} \in X } \exp \left( -2\pi i \mathbf{k}^{\top} \mathbf{x} \right) \right|^{2}
\end{equation}
\begin{align}
    \mathcal{L}^{\ast}
    =
    \left\\{
        \mathbf{M}^{\top} \mathbf{B}
        \mid
        \mathbf{M} \in \mathbb{Z}^{3}, F(\mathbf{k} + \mathbf{B}^{-1}\mathbf{M}^{\top}\mathbf{B}) = F(\mathbf{k}) \, (\forall \mathbf{k})
    \right\\}
    \\
    =
    \left\\{
        \mathbf{M}^{\top} \mathbf{B}
        \mid
        \mathbf{M} \in \mathbb{Z}^{3}, F(\mathbf{B}^{-1}\mathbf{M}^{\top}\mathbf{B}) = N^{2}
    \right\\}
    =
    \left\\{
        \mathbf{M}^{\top} \mathbf{B}
        \mid
        \mathbf{M} \in \mathbb{Z}^{3},
        ( \mathbf{B}^{-1}\mathbf{M}^{\top}\mathbf{B} )^{\top} \mathbf{x} \in \mathbb{Z}
        \, (\forall \mathbf{x} \in X)
    \right\\}
\end{align}
