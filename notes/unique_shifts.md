---
title: "Listing nonequivalent terminations of free surfaces"
layout: post
use_math: true
---

Some of terminations of free surfaces are identical under symmetry operations of given unit cell (`ucell`).
`ucell` is enlarged by `uvws` matrix, $\mathbf{M}$,  to accommodate given `hkl` plane, which we refer as `rcell`:
Let $\mathbf{A}\_{ \mathrm{rcell} }$ be column-wise lattice vectors (that is, $\mathbf{A}\_{ \mathrm{rcell} }[i, :]$ is the $i$th lattice vector).
\begin{equation}
  \mathbf{A}\_{ \mathrm{rcell} } = \mathbf{M} \mathbf{A}_{ \mathrm{ucell} } \mathbf{T}^{\top},
\end{equation}
where $\mathbf{T}$ is a transformation matrix of axes.

### `FreeSurface.__init__`
To enumerate all terminations, we first get unique coordinates of `rcell` normal to `hkl` axis.
Then, we only need to consider middle plane locating at the consecutive unique coordinates, which we refer as `shifts`.

### `region.Plane.Plane.isclose`
Next, we consider crystal planes passing `shifts`.
Crystal plane $(\mathbf{n}, \mathbf{s})$ can be specified with normal direction $\mathbf{n}$ and one of passed point $\mathbf{p}$
\begin{equation}
    (\mathbf{n}, \mathbf{s}) = \left\\{ \mathbf{r} | (\mathbf{r} - \mathbf{p}) \cdot \mathbf{n} > 0 \right\\}.
\end{equation}
Two crystal planes $(\mathbf{n}, \mathbf{s})$ and $(\mathbf{n}', \mathbf{s}')$ are the same if
\begin{equation}
    \mathbf{n} = \mathbf{n}'
\end{equation}
and
\begin{equation}
    \mathbf{n} \cdot (\mathbf{s} - \mathbf{s}') = 0.
\end{equation}

### `region.Plane.Plane.operate` and `is_equivalent_by_primitive_vects`

A symmetry operation $\\{ \mathbf{R} | \mathbf{v} \\}$ in cartesian coordinates transforms crystal plane $(\mathbf{n}, \mathbf{s})$ into
\begin{equation}
    \\{ \mathbf{R} | \mathbf{v} \\} (\mathbf{n}, \mathbf{s})
    = \left\\{ \mathbf{Rr} + \mathbf{v} | (\mathbf{r} - \mathbf{s}) \cdot \mathbf{n} > 0 \right\\}
    = (\mathbf{Rn}, \mathbf{Rs} + \mathbf{v}).
\end{equation}
Thus, two crystal planes $(\mathbf{n}, \mathbf{s})$ and $(\mathbf{n}', \mathbf{s}')$ with the same normal direction are symmetrically equivalent if there exists some symmetry operation of `rcell`, $\\{ \mathbf{R} | \mathbf{v} + \mathbf{T} \mathbf{A}\_{\mathrm{ucell}}^{\top} \mathbf{m} \\}$, such that
\begin{equation}
    \mathbf{Rn} = \mathbf{n}'
\end{equation}
and
\begin{equation}
    \mathbf{Rs} + \mathbf{v} + \mathbf{T} \mathbf{A}_{\mathrm{ucell}}^{\top} \mathbf{m} = \mathbf{s}',
\end{equation}
where $\mathbf{m}$ is `trial_image`, integer vector.

Coset representative of symmetry operations $\\{ \mathbf{R} | \mathbf{v} \\}$ can be calculated with spglib.
We also need to consider translation symmetry of `ucell` to match two crystal planes.
(I cannot come up with another way to find translationally equivalent planes. There may be a cleverer way not to use heuristics like `trial_image`.)
