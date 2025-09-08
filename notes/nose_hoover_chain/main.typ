#import "@preview/ctheorems:1.1.2": *
#import "@preview/physica:0.9.3": *
#show: thmrules

#set heading(numbering: "1.")
#set par(
  leading: 1em,
  justify: true,
  first-line-indent: 1em,
)
#set enum(numbering: "(1)")
#set math.equation(numbering: "(1)")

#set document(
  title: "The canonical and isobaric ensembles via molecular dynamics",
  author: "Kohei Shinohara (@lan496)",
)

#outline()

= The canonical and isobaric ensembles via molecular dynamics

== Classical non-Hamiltonian statistical mechanics

Consider a dynamical system $dot(bold(x)) = bold(xi)(bold(x))$.
We define the compressibility as
$
  kappa(bold(x)_t) &:= bold(nabla)_(bold(x)_t) dot dot(bold(x)_t) =: dv(, t) w(bold(x)_t).
$
With $sqrt(g(bold(x))) := e^(-w(bold(x)))$, generalized Liouville's Theorem states that
$
  sqrt(g(bold(x)_t)) d bold(x)_t = sqrt(g(bold(x)_0)) d bold(x)_0.
$

The Liouville operator is defined as
$
  i cal(L) &:= bold(xi)(bold(x)) dot bold(nabla)_(bold(x)).
$
Since $dot(bold(x)_t) = i L bold(x)_t$, we formally write
$
  bold(x)_t = e^( i t cal(L) ) bold(x)_0.
$

== Matrix exponential

For square matrices $bold(A)$ and $bold(B)$, we define the 2nd order integrator as
$
  S_2 (lambda) := e^(frac(lambda, 2) bold(B)) e^(lambda bold(A)) e^(frac(lambda, 2) bold(B)) \
  S_2 (lambda) = e^(lambda (bold(A) + bold(B)))  + O(lambda^3).
$

The fourth order integrator #cite(label("YOSHIDA1990262"))
$
  S_4 (lambda) := S_2 (x_3 lambda) S_2 (x_2 lambda) S_2 (x_1 lambda) \
  x_1 = x_3 := frac(1, 2 - 2^(1/3)) \
  x_2 := -frac(2^(1/3), 2 - 2^(1/3)) \
  S_4 (lambda) = e^(lambda (bold(A) + bold(B)))  + O(lambda^5).
$

== Canonical ensembles

=== Nosé-Hoover chain

Nosé-Hoover chain equations:
$
  dot(bold(r))_i &= frac( bold(p)_i, m_i ) \
  dot(bold(p))_i &= bold(F)_i - frac( p_(eta_1), Q_1 ) bold(p)_i \
  dot(eta)_j     &= frac( p_(eta_j), Q_j ) quad (j = 1, dots, M) \
  dot(p)_(eta_1) &= sum_(i=1)^N frac( bold(p)_i^2, m_i ) - d N k T - frac( p_(eta_2), Q_2 ) p_(eta_1) \
  dot(p)_(eta_j) &= frac( p_(eta_(j-1))^2, Q_(j-1) ) - k T - frac( p_(eta_(j+1)), Q_(j+1) ) p_(eta_j) quad (j = 2, dots, M-1) \
  dot(p)_(eta_M) &= frac( p_(eta_(M-1))^2, Q_(M-1) ) - k T
$

Ref.~#cite(label("10.1063/1.463940")) suggests
$
  Q_1 &= d N k T tau^2 \
  Q_j &= k T tau^2 quad (j = 2, dots, M).
$

=== Conserved quantities of Nosé-Hoover chain equations

Nosé-Hoover chain equations conserves
$
  H' := cal(H)(r^N, p^N) + sum_(j=1)^M frac( p_(eta_j)^2, 2 Q_j ) + d N k T eta_1 + k T eta_c.
$
where $eta_c := sum_(j=2)^M eta_j$.
In the absence of external forces ($sum_i bold(F)_i = 0$), the center-of-mass momentum $bold(P) := sum_i bold(p)_i$ also has a conserved quantity
$
  bold(K) := bold(P) e^(eta_1).
$

=== Microcanonical distribution given by Nosé-Hoover chain equations

The EOM gives the compressibility
$
  kappa(bold(x)) = -d N dot(eta)_1 - dot(eta_c).
$
Let us consider the distribution function traced over the extended variables,
$
  Z_(V, T)(r^N, p^N)
    &:= integral d p_eta^M d eta^M e^(d N eta_1 + eta_c) delta( cal(H)(r^N, p^N) + sum_(j=1)^M frac( p_(eta_j)^2, 2 Q_j ) + d N k T eta_1 + k T eta_c - H' ) \
    &= (product_(j=1)^M sqrt( 2 pi k T Q_j ) ) exp( -frac(1, k T) ( cal(H)(r^N, p^N) - H' ) ) integral d eta_1 \
    &prop exp( -frac(1, k T) cal(H)(r^N, p^N) ). \
$
This shows that the Nosé-Hoover chain equations generates the canonical ensemble in the physical phase space.

=== Integrating the Nosé-Hoover chain equations

The Liouville operator
$
  i L       &:= i L_"NHC" + i L_1 + i L_2 \
  i L_1     &:= sum_(i=1)^N frac( bold(p)_i, m_i ) dot pdv(, bold(r)_i) \
  i L_2     &:= sum_(i=1)^N bold(F)_i dot pdv(, bold(p)_i) \
  i L_"NHC" &:= - sum_(i=1)^N frac(p_(eta_1), Q_1) bold(p)_i dot pdv(, bold(p)_i)
                + sum_(j=1)^M frac(p_(eta_j), Q_j) pdv(, eta_j)
                + sum_(j=1)^(M-1) ( G_j - p_(eta_j) frac(p_(eta_(j+1)), Q_(j+1)) ) pdv(, p_(eta_j))
                + G_M pdv(, p_(eta_M)) \
  G_1       &:= sum_(i=1)^N frac( bold(p)_i^2, m_i ) - d N k T \
  G_j       &:= frac(p_(eta_(j-1))^2, Q_(j-1)) - k T quad (j = 2, dots, M) \
$

$
  e^(i L Delta t) = e^(i L_"NHC" frac(Delta t, 2)) e^(i L_2 frac(Delta t, 2)) e^(i L_1 Delta t) e^(i L_2 frac(Delta t, 2)) e^(i L_"NHC" frac(Delta t, 2)) + O(Delta t^3).
$

$
  e^(i L_1 Delta t) mat(bold(r)_i; bold(p)_i; eta_j; bold(p)_(eta_j) )
    &= mat(
      bold(r)_i + frac(bold(p)_i, m_i) Delta t;
      bold(p)_i;
      eta_j;
      bold(p)_(eta_j)
    )
$
$
  e^(i L_2 frac(Delta t, 2)) mat(bold(r)_i; bold(p)_i; eta_j; bold(p)_(eta_j))
    &= mat(
      bold(r)_i;
      bold(p)_i + bold(F)_i frac(Delta t, 2);
      eta_j;
      bold(p)_(eta_j)
    )
$
$
  e^(i L_"NHC" frac(Delta t, 2))
    &= ( e^(i L_"NHC" frac(Delta t, 2 n)) )^n \
  e^(i L_"NHC" frac(Delta t, 2 n))
    &= S_4^"NHC" (frac(Delta t, 2 n)) + O((frac(Delta t, n))^5) \
  S_4^"NHC" (frac(Delta t, 2 n))
    &:= product_(alpha=1)^3 S_2^"NHC" (x_alpha frac(Delta t, 2 n))
      quad (delta_alpha := x_alpha frac(Delta t, 2 n)) \
  S_2^"NHC" (delta_alpha)
    &:= exp( frac(delta_alpha, 2) G_M pdv(, p_(eta_M)) ) \
      &times product_(j=M-1)^1 (
        exp( -frac(delta_alpha, 4) frac( p_(eta_(j+1)), Q_(j+1)) p_(eta_j) pdv(, p_(eta_j)) )
        exp( frac(delta_alpha, 2) G_j pdv(, p_(eta_j)))
        exp( -frac(delta_alpha, 4) frac( p_(eta_(j+1)), Q_(j+1)) p_(eta_j) pdv(, p_(eta_j)) )
      ) \
      &times product_(i=1)^N exp( -delta_alpha frac(p_(eta_1), Q_1) bold(p)_i dot pdv(, bold(p)_i) ) \
      &times product_(j=1)^M exp( delta_alpha frac(p_(eta_j), Q_j) pdv(, eta_j) ) \
      &times product_(j=1)^(M-1) (
        exp( -frac(delta_alpha, 4) frac( p_(eta_(j+1)), Q_(j+1)) p_(eta_j) pdv(, p_(eta_j)) )
        exp( frac(delta_alpha, 2) G_j pdv(, p_(eta_j)))
        exp( -frac(delta_alpha, 4) frac( p_(eta_(j+1)), Q_(j+1)) p_(eta_j) pdv(, p_(eta_j)) )
      ) \
      &times exp( frac(delta_alpha, 2) G_M pdv(, p_(eta_M)) )
$

Here, we use the following formula to evaluate the actions,
$
exp( c x pdv(, x) ) f(x) = f(x e^c).
$

== The isobaric ensembles

Refs.~#cite(label("10.1063/1.467468"))

=== Instantaneous stress tensor

Let $bold(h)$ be right-handed row-major basis vectors.
// We write the unit vector parallel to the $alpha$th basis vector $bold(h)_(alpha :)$ as $hat(bold(e))_alpha$.

Instantaneous stress tensor
$
  cal(P)^"int"_(alpha beta) = frac(1, det bold(h)) sum_(i=1)^N [
    frac( p_(i alpha) p_(i beta), m_i) + F_(i alpha) r_(i beta)
  ] - frac(1, det bold(h)) sum_(gamma=1)^3 pdv(U, h_(alpha gamma)) h_(gamma beta).
$

=== Isotropic volume fluctuations

==== MTK equations for isotropic volume fluctuations

MTK equations:
$
  dot(bold(r))_i &= frac( bold(p)_i, m_i ) + frac(p_epsilon, W) bold(r)_i \
  dot(bold(p))_i &= tilde(bold(F))_i - (1 + frac(d, N_f)) frac(p_epsilon, W) bold(p)_i - frac( p_(eta_1), Q_1 ) bold(p)_i \
  dot(V)         &= frac(d V, W) p_epsilon \
  dot(p)_epsilon &= d V (cal(P)^"int" - P) + frac(d, N_f) sum_(i=1)^N frac(bold(p)_i^2, m_i) - frac(p_(xi_1), Q'_1) p_epsilon \
  dot(eta)_j     &= frac( p_(eta_j), Q_j ) \
  dot(xi)_j      &= frac( p_(xi_j), Q'_j )   \
  dot(p)_(eta_j) &= G_j - frac( p_(eta_(j+1)), Q_(j+1) ) p_(eta_j) quad (j = 1, dots, M-1) \
  dot(p)_(eta_M) &= G_M \
  dot(p)_(xi_j) &= G'_j - frac( p_(xi_(j+1)), Q'_(j+1) ) p_(xi_j) quad (j = 1, dots, M-1) \
  dot(p)_(xi_M) &= G'_M \
$
where
$
  G'_1 &:= frac(p_epsilon^2, W) - k T \
  G'_j &:= frac(p_(xi_(j-1))^2, Q'_(j-1)) - k T quad (j = 2, dots, M).
$

Ref.~#cite(label("10.1063/1.467468")) suggests to set
$
  W  &= (N_f + d) k T tau^2 \
  Q'_1 &= d^2 k T tau^2 \
  Q'_j &= k T tau^2 quad (j = 2, dots, M),
$
where $tau$ is a characteristic time scale for barostat.

==== Conserved quantities of MTK equations

The conserved energy
$
  H' := cal(H) (r, p) + frac( p_epsilon^2, 2W) + P V
    + sum_(j=1)^M ( frac(p_(eta_j)^2, 2 Q_j) + frac(p_(xi_j)^2, 2 Q'_j) + k T xi_j )
    + N_f k T eta_1 + k T eta_c,
$
where $eta_c := sum_(j=2)^M eta_j$.

In the absence of external forces ($sum_i bold(F)_i = 0$), the center-of-mass momentum $bold(P) := sum_i bold(p)_i$ also has a conserved quantity
$
  bold(K) := bold(P) exp ( (1 + frac(d, N_f) ) epsilon + eta_1 ),
$
where $epsilon := 1/d log V/V_0$ with some reference volume $V_0$.

==== Microcanonical distribution given by MTK equations

Let $Q(N, V, T)$ be a partition function for NVT ensemble.
The partition function for isotropic-NPT ensemble is defined as
$
  Delta(N, P, T) := 1/V_0 integral d V e^(-beta P V) Q(N, V, T).
$

The EOM gives the compressibility
$
  kappa(bold(x)) &= -dv(, t) ( d N eta_1 + eta_c + xi_1 + xi_c ) \
  therefore sqrt(g(bold(x))) &= e^( d N eta_1 + eta_c + xi_1 + xi_c ),
$
where $xi_c := sum_(j=2)^M xi_j$.
Because this metric $sqrt(g (bold(x))) d bold(x)$ does not depends on physical variables, the extended variables are traced out in $Delta(N, P, T)$.

==== Integrating the MTK equations for isotropic volume fluctuations

$
  i L               &:= i L_1 + i L_2 + i L_(epsilon, 1) + i L_(epsilon, 2) + i L_("NHC-baro") + i L_("NHC-thermo") \
  i L_1             &:= sum_(i=1)^N ( frac( bold(p)_i, m_i ) + frac(p_epsilon, W) bold(r)_i ) dot pdv(, bold(r)_i) \
  i L_2             &:= sum_(i=1)^N ( tilde(bold(F))_i - (1 + frac(d, N_f)) frac(p_epsilon, W) bold(p)_i ) dot pdv(, bold(p)_i) \
  i L_(epsilon, 1)  &:= frac(p_epsilon, W) pdv(, epsilon) \
  i L_(epsilon, 2)  &:= G_epsilon pdv(, p_epsilon) \
  i L_"NHC-thermo"  &:= - sum_(i=1)^N frac(p_(eta_1), Q_1) bold(p)_i dot pdv(, bold(p)_i)
                      + sum_(j=1)^M frac(p_(eta_j), Q_j) pdv(, eta_j)
                      + sum_(j=1)^(M-1) ( G_j - p_(eta_j) frac(p_(eta_(j+1)), Q_(j+1)) ) pdv(, p_(eta_j))
                      + G_M pdv(, p_(eta_M)) \
  i L_"NHC-baro"    &:= - frac(p_(xi_1), Q'_1) p_epsilon pdv(, p_epsilon)
                      + sum_(j=1)^M frac(p_(xi_j), Q'_j) pdv(, xi_j)
                      + sum_(j=1)^(M-1) ( G'_j - p_(xi_j) frac(p_(xi_(j+1)), Q'_(j+1)) ) pdv(, p_(xi_j))
                      + G'_M pdv(, p_(xi_M)) \
$
with
$
  epsilon &:= 1/d ln V/V_0 \
  cal(P)^"int" &:= 1/d Tr[cal(bold(P))^"int"] = 1/(d V) sum_(i=1)^N (frac(bold(p)_i^2, m_i) + bold(r)_i dot bold(F)_i) \
  G_epsilon &:= d V (cal(P)^"int" - P) + frac(1, N) sum_(i=1)^N frac(bold(p)_i^2, m_i).
$

$
  e^(i L Delta t)
    &=
      e^(i L_"NHC-baro" frac(Delta t, 2)) e^(i L_"NHC-thermo" frac(Delta t, 2)) \
      &times e^(i L_(epsilon, 2) frac(Delta t, 2)) e^(i L_2 frac(Delta t, 2)) \
      &times e^(i L_(epsilon, 1) Delta t) e^(i L_1 Delta t) \
      &times e^(i L_2 frac(Delta t, 2)) e^(i L_(epsilon, 2) frac(Delta t, 2)) \
      &times e^(i L_"NHC-thermo" frac(Delta t, 2)) e^(i L_"NHC-baro" frac(Delta t, 2)) + O(Delta t^3).
$

$
  e^(i L_1 Delta t) bold(r)_i
    &= exp(Delta t (frac(bold(p)_i, m_i) + frac(p_epsilon, W) bold(r)_i ) dot pdv(, bold(r)_i)) bold(r)_i \
    &= bold(r)_i e^(frac(p_epsilon Delta t, W)) + Delta t frac(bold(p)_i, m_i) "exprel"(frac(p_epsilon Delta t, W)) \
$

$
  e^(i L_2 frac(Delta t, 2)) bold(p)_i
    &= exp( frac(Delta t, 2) ( tilde(bold(F))_i - (1 + frac(d, N_f)) frac(p_epsilon, W) bold(p)_i ) dot pdv(, bold(p)_i)) bold(p)_i \
    &= bold(p)_i e^(-frac(kappa Delta t, 2 W))
      + frac(Delta t, 2) tilde(bold(F))_i "exprel"(-frac(kappa Delta t, 2 W))
    \
  kappa &:= (1 + frac(d, N_f)) p_epsilon
$

=== Anisotropic cell fluctuations

==== MTK equations for anisotropic cell fluctuations

MTK equations:
$
  dot(bold(r))_i &= frac( bold(p)_i, m_i ) + frac(bold("p")_g, W_g) bold(r)_i \
  dot(bold(p))_i &= tilde(bold(F))_i - (bold("p")_g + frac("Tr"[bold("p")_g], N_f) bold("I")) frac(bold(p)_i, W_g) - frac( p_(eta_1), Q_1 ) bold(p)_i \
  dot(bold("h"))   &= frac( bold("h") bold("p")_g , W_g) \
  dot(bold("p"))_g &= det[bold("h")] (cal(bold(P))^"int" - P bold("I")) + frac(1, N_f) sum_(i=1)^N frac(bold(p)_i^2, m_i) bold("I") - frac(p_(xi_1), Q'_1) bold("p")_g \
  dot(eta)_j     &= frac( p_(eta_j), Q_j ) \
  dot(xi)_j      &= frac( p_(xi_j), Q'_j )   \
  dot(p)_(eta_j) &= G_j - frac( p_(eta_(j+1)), Q_(j+1) ) p_(eta_j) quad (j = 1, dots, M-1) \
  dot(p)_(eta_M) &= G_M \
  dot(p)_(xi_j) &= G'_j - frac( p_(xi_(j+1)), Q'_(j+1) ) p_(xi_j) quad (j = 1, dots, M-1) \
  dot(p)_(xi_M) &= G'_M \
$
where
$
  G_1 &:= sum_(i=1)^N frac( bold(p)_i^2, m_i ) - N_f k T \
  G_j &:= frac(p_(eta_(j-1))^2, Q_(j-1)) - k T quad (j = 2, dots, M) \
  G'_1 &:= frac("Tr"[bold("p")_g^top bold("p")_g], W_g) - d^2 k T \
  G'_j &:= frac(p_(xi_(j-1))^2, Q'_(j-1)) - k T quad (j = 2, dots, M) \
$

Ref.~#cite(label("10.1063/1.467468")) suggests to set
$
  W_g  &= frac(N_f + d, d) k T tau^2 \
  Q'_1 &= d^2 k T tau^2 \
  Q'_j &= k T tau^2 quad (j = 2, dots, M),
$
where $tau$ is a characteristic time scale for barostat.
$d^2$ in $Q'_1$ should be substituted with the degree of freedoms in basis vectors.

==== Conserved quantities of anisotropic MTK equations

The conserved energy
$
  H' &:= cal(H) (r, p) + frac( "Tr"[bold("p")_g^top bold("p")_g], 2 W_g) + P det[bold("h")] \
    &+ sum_(j=1)^M ( frac(p_(eta_j)^2, 2 Q_j)
    + frac(p_(xi_j)^2, 2 Q'_j))
    + N_f k T eta_1
    + d^2 k T xi_1
    + k T sum_(j=2)^M (eta_j + xi_j)
$

In the absence of external forces ($sum_i bold(F)_i = 0$), the center-of-mass momentum $bold(P) := sum_i bold(p)_i$ also has a conserved quantity
$
  bold(K) := bold("h") bold(P) (det bold("h"))^(1\/N_f) e^(eta_1).
$

==== Microcanonical distribution given by anisotropic MTK equations

Let $Q(N, V, T)$ be a partition function for NPT ensemble.
The partition function for anisotropic-NPT ensemble is defined as
$
  Delta(N, P, T)
    &:= 1/V_0 integral d V e^(-beta P V) integral d bold("h")_0 Q(N, V bold("h")_0, T) delta(det bold("h")_0 - 1) \
    &= 1/V_0 integral d V integral d bold("h") V^(1-d) e^(-beta P V) Q(N, bold("h"), T) delta(det bold("h") - V)
$

The EOM gives the compressibility
$
  kappa(bold(x))
    &= -dv(, t) ( (1-d) ln det bold("h") + d N eta_1 + eta_c + d^2 xi_1 + xi_c ) \
  therefore sqrt(g(bold(x)))
    &= (det bold("h"))^(1-d) e^( d N eta_1 + eta_c + d^2 xi_1 + xi_c ).
$
Because this metric $sqrt(g (bold(x))) d bold(x)$ depends on physical variables as same as the integral in $Delta (N, P, T)$, the extended variables are traced out in $Delta(N, P, T)$.

==== Integrating the MTK equations for anisotropic cell fluctuations

Ref.~#cite(label("Tuckerman_2006"))

$
  i L               &:= i L_1 + i L_2 + i L_(g, 1) + i L_(g, 2) + i L_("NHC-baro") + i L_("NHC-thermo") \
  i L_1             &:= sum_(i=1)^N ( frac( bold(p)_i, m_i ) + frac(bold("p")_g, W_g) bold(r)_i ) dot pdv(, bold(r)_i) \
  i L_2             &:= sum_(i=1)^N ( tilde(bold(F))_i - (bold("p")_g + frac("Tr"[bold("p")_g], N_f) bold("I")) frac(bold(p)_i, W_g) ) dot pdv(, bold(p)_i) \
  i L_(g, 1)        &:= frac(bold("h") bold("p")_g , W_g) dot.circle pdv(, bold("h")) \
  i L_(g, 2)        &:= bold("G")_g dot.circle pdv(, bold("p")_g) \
  i L_"NHC-thermo"  &:= - sum_(i=1)^N frac(p_(eta_1), Q_1) bold(p)_i dot pdv(, bold(p)_i)
                      + sum_(j=1)^M frac(p_(eta_j), Q_j) pdv(, eta_j)
                      + sum_(j=1)^(M-1) ( G_j - p_(eta_j) frac(p_(eta_(j+1)), Q_(j+1)) ) pdv(, p_(eta_j))
                      + G_M pdv(, p_(eta_M)) \
  i L_"NHC-baro"    &:= - frac(p_(xi_1), Q'_1) bold("p")_g dot.circle pdv(, bold("p")_g)
                      + sum_(j=1)^M frac(p_(xi_j), Q'_j) pdv(, xi_j)
                      + sum_(j=1)^(M-1) ( G'_j - p_(xi_j) frac(p_(xi_(j+1)), Q'_(j+1)) ) pdv(, p_(xi_j))
                      + G'_M pdv(, p_(xi_M)) \
$
with
$
  bold("G")_g &:= det[bold("h")] (cal(bold(P))^"int" - P bold("I"))
    + frac(1, N_f) sum_(i=1)^N frac(bold(p)_i^2, m_i) bold("I ").
$

$
  e^(i L Delta t)
    &=
      e^(i L_"NHC-baro" frac(Delta t, 2)) e^(i L_"NHC-thermo" frac(Delta t, 2)) \
      &times e^(i L_(g, 2) frac(Delta t, 2)) e^(i L_2 frac(Delta t, 2)) \
      &times e^(i L_(g, 1) Delta t) e^(i L_1 Delta t) \
      &times e^(i L_2 frac(Delta t, 2)) e^(i L_(g, 2) frac(Delta t, 2)) \
      &times e^(i L_"NHC-thermo" frac(Delta t, 2)) e^(i L_"NHC-baro" frac(Delta t, 2)) + O(Delta t^3).
$

The actions of $e^(i L_"NHC-baro" frac(Delta t, 2))$ and $e^(i L_"NHC-thermo" frac(Delta t, 2))$ can be evaluated similarly to the Nosé-Hoover chain equations.
The action of $e^(i L_(g, 2) frac(Delta t, 2))$ just translates $bold("p")_g$.

Since $bold("p")_g$ is a symmetric real matrix, we can diagonalize it as
$
  bold("p")_g = sum_(mu=1)^3 lambda_mu bold(u)_mu bold(u)_mu^top \
  bold(U) := (bold(u)_1, bold(u)_2, bold(u)_3) \
  bold(U) mat(lambda_1, 0, 0; 0, lambda_2, 0; 0, 0, lambda_3) bold(U)^top = bold("p")_g \
$
with
$
  lambda_mu in bb(R) \
  bold(u)_mu^top bold(u)_nu &= delta_(mu nu).
$

$
  e^(i L_"NHC-baro" frac(Delta t, 2))
    &= ( e^(i L_"NHC-baro" frac(Delta t, 2 n)) )^n \
  e^(i L_"NHC-baro" frac(Delta t, 2 n))
    &= S_4^"NHC-baro" (frac(Delta t, 2 n)) + O((frac(Delta t, n))^5) \
  S_4^"NHC-baro" (frac(Delta t, 2 n))
    &:= product_(alpha=1)^3 S_2^"NHC-baro" (x_alpha frac(Delta t, 2 n))
      quad (delta_alpha := x_alpha frac(Delta t, 2 n)) \
  S_2^"NHC-baro" (delta_alpha)
    &:= exp( frac(delta_alpha, 2) G'_M pdv(, p_(xi_M)) ) \
      &times product_(j=M-1)^1 (
        exp( -frac(delta_alpha, 4) frac( p_(xi_(j+1)), Q'_(j+1)) p_(xi_j) pdv(, p_(xi_j)) )
        exp( frac(delta_alpha, 2) G'_j pdv(, p_(xi_j)))
        exp( -frac(delta_alpha, 4) frac( p_(xi_(j+1)), Q'_(j+1)) p_(xi_j) pdv(, p_(xi_j)) )
      ) \
      &times exp( -delta_alpha frac(p_(xi_1), Q'_1) bold("p "_g) dot.circle pdv(, bold("p ")_g) ) \
      &times product_(j=1)^M exp( delta_alpha frac(p_(xi_j), Q'_j) pdv(, xi_j) ) \
      &times product_(j=1)^(M-1) (
        exp( -frac(delta_alpha, 4) frac( p_(xi_(j+1)), Q'_(j+1)) p_(xi_j) pdv(, p_(xi_j)) )
        exp( frac(delta_alpha, 2) G'_j pdv(, p_(xi_j)))
        exp( -frac(delta_alpha, 4) frac( p_(xi_(j+1)), Q'_(j+1)) p_(xi_j) pdv(, p_(xi_j)) )
      ) \
      &times exp( frac(delta_alpha, 2) G'_M pdv(, p_(xi_M)) )
$

==== Actions of $e^(i L_1 Delta t)$ and $e^(i L_2 frac(Delta t, 2))$

$
  bold(x)_i := bold(U)^top bold(r)_i \
  e^(i L_1 Delta t) bold(r)_i
    &= exp(Delta t (frac(bold(p)_i, m_i) + 1/W_g bold("p")_g bold(r)_i ) dot pdv(, bold(r)_i)) bold(r)_i \
    &= bold(U) exp(Delta t (frac(bold(p)_i, m_i) + 1/W_g bold("p")_g bold(r)_i ) dot pdv(, bold(r)_i)) bold(x)_i \
    &= bold(U) exp(Delta t ( frac(bold(U)^top bold(p)_i, m_i) + 1/W_g bold(U)^top bold("p")_g bold(U) bold(x)_i ) dot pdv(, bold(x)_i)) bold(x)_i \
    &= bold(U) (
      exp(Delta t ( frac([bold(U)^top bold(p)_i]_alpha, m_i) + 1/W_g lambda_alpha x_(i alpha) ) pdv(, x_(i alpha))) x_(i alpha)
    )_(alpha=1, 2, 3) \
    &= bold(U) (
      x_(i alpha) e^(frac(lambda_alpha Delta t, W_g))
      + Delta t frac([bold(U)^top bold(p)_i]_alpha, m_i) "exprel"(frac(lambda_alpha Delta t, W_g))
    )_(alpha=1, 2, 3) \
  "exprel"(x) &:= frac( e^x - 1, x) \
$

Similarly
$
  bold(y)_i := bold(U)^top bold(p)_i \
  e^(i L_2 frac(Delta t, 2)) bold(p)_i
    &= exp( frac(Delta t, 2) ( tilde(bold(F))_i - 1/W_g (bold("p")_g + frac("Tr"[bold("p")_g], N_f) bold("I")) bold(p)_i ) dot pdv(, bold(p)_i)) bold(p)_i \
    &= bold(U) exp( frac(Delta t, 2) ( tilde(bold(F))_i - 1/W_g (bold("p")_g + frac("Tr"[bold("p")_g], N_f) bold("I")) bold(p)_i ) dot pdv(, bold(p)_i)) bold(y)_i \
    &= bold(U) exp( frac(Delta t, 2) ( bold(U)^top tilde(bold(F))_i - 1/W_g bold(U)^top (bold("p")_g + frac("Tr"[bold("p")_g], N_f) bold("I")) bold(U) bold(y)_i ) dot pdv(, bold(y)_i)) bold(y)_i \
    &= bold(U) (
      exp(
        frac(Delta t, 2) (
          [bold(U)^top tilde(bold(F))_i]_alpha
          - 1/W_g (
            lambda_alpha + frac("Tr"[bold("p")_g], N_f)
          ) y_(i alpha)
        )
        pdv(, y_(i alpha))
      )
      y_(i alpha)
    )_(alpha=1, 2, 3) \
    &= bold(U) (
      y_(i alpha) e^(-frac(kappa_alpha Delta t, 2 W_g))
      + frac(Delta t, 2) [bold(U)^top tilde(bold(F))_i]_alpha "exprel"(-frac(kappa_alpha Delta t, 2 W_g))
    )_(alpha=1, 2, 3) \
  kappa_alpha &:= lambda_alpha + frac("Tr"[bold("p")_g], N_f)
$

==== Action of $e^(i L_(g, 1) Delta t)$

$
  bold("n") := bold("h") bold("U") \
  e^(i L_(g, 1) Delta t) bold("h")
    &=exp(Delta t frac(bold("h") bold("p")_g , W_g) dot.circle pdv(, bold("h"))) bold("h") \
    &=exp(frac(Delta t, W_g) "Tr"[(bold("h") bold("p")_g )^top pdv(, bold("h"))]) bold("h") \
    &=exp(frac(Delta t, W_g) "Tr"[bold("p")_g bold("U") bold("n")^top  pdv(, bold("n")) bold("U")^top ]) bold("n") bold("U")^top \
    &=(product_(mu alpha) exp(frac(Delta t lambda_alpha, W_g) n_(mu alpha) pdv(, n_(mu alpha))) bold("n") )bold("U")^top \
    &=(
      e^(frac(Delta t lambda_alpha, W_g)) n_(mu alpha)
    )_(mu alpha) bold("U")^top \
$

=== Cell fluctuations with mask

==== MTK equations

Consider the case when the cell fluctuations are allowed only $n_c$ axes of the cell matrix $bold("h")$.
For $c=1, ..., n_c$, let $p_c$ be the momentum conjugate to the $c$th axis of $bold("h")$.

$
  bold("p")_g = sum_c p_c bold(e)_c bold(e)_c^top
$

EOM are the same as the anisotropic MTK equations except for
$
  dot(p)_c
    &= det[bold("h")] dot bold(e)_c^top (cal(bold(P))^"int" - P bold("I")) bold(e)_c
        + frac(1, N_f) sum_(i=1)^N frac(bold(p)_i^2 , m_i)
        - frac(p_(xi_1), Q'_1) p_c
      quad (c = 1, dots, n_c) \
  G'_1 &:= sum_c frac(p_c^2, W_g) - n_c k T \
  // W_g  &= frac(N_f + d, d) k T tau^2 \
  Q'_1 &= n_c k T tau^2,
$
where $tau$ is a characteristic time scale for barostat.

==== Conserved quantities

The conserved energy
$
  H'
    &:= cal(H) (r, p) + sum_c frac( p_c^2, 2 W) + P det[bold("h")] \
    &+ sum_(j=1)^M ( frac(p_(eta_j)^2, 2 Q_j)
    + frac(p_(xi_j)^2, 2 Q'_j))
    + N_f k T eta_1
    + n_c k T xi_1
    + k T sum_(j=2)^M (eta_j + xi_j)
$

==== Integrating the MTK equations

$
  i L               &:= i L_1 + i L_2 + i L_(g, 1) + i L_(g, 2) + i L_("NHC-baro") + i L_("NHC-thermo") \
  i L_(g, 2)        &:= sum_c G_c dot.circle pdv(, p_c) \
$
with
$
  G_c
    &:= det[bold("h")] dot bold(e)_c^top (cal(bold(P))^"int" - P bold("I")) bold(e)_c
      + frac(1, N_f) sum_(i=1)^N frac(bold(p)_i^2, m_i).
$


#bibliography("references.bib")
