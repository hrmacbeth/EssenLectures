/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
-/
import Mathlib.Topology.MetricSpace.Isometry
import GromovHyperbolicity.Prereqs.GeodesicSpace
import Mathlib.Topology.MetricSpace.HausdorffDistance

/- # Quasi-isometries -/

open Set Metric
variable {X : Type*} [MetricSpace X] {Y : Type*} [MetricSpace Y]

/-- A $(\lambda, C)$ quasi-isometry is a function which behaves like an isometry, up to
an additive error $C$ and a multiplicative error $\lambda$. It can be very different from an
isometry on small scales (for instance, the function integer part is a quasi-isometry between
`ℝ` and `ℤ`), but on large scales it captures many important features of
isometries.

When the space is unbounded, one checks easily that $C \geq 0$ and $\lambda \geq 1$. As this
is the only case of interest (any two bounded sets are quasi-isometric), we incorporate
this requirement in the definition. -/
structure QuasiIsometryOn (lambda C : ℝ) (s : Set X) (f : X → Y) : Prop :=
  (one_le_lambda : 1 ≤ lambda)
  (C_nonneg : 0 ≤ C)
  (upper_bound {x y : X} (_ : x ∈ s) (_ : y ∈ s) : dist (f x) (f y) ≤ lambda * dist x y + C)
  (lower_bound {x y : X} (_ : x ∈ s) (_ : y ∈ s) : (1/lambda) * dist x y - C ≤ dist (f x) (f y))

theorem QuasiIsometryOn.mono {lambda C : ℝ} {s : Set X} {f : X → Y}
    (hf : QuasiIsometryOn lambda C s f) {t : Set X} (hts : t ⊆ s) :
    QuasiIsometryOn lambda C t f :=
  sorry

/-! ## Quasi-geodesics -/

/-- A quasi-geodesic is a quasi-isometric embedding of a real segment into a metric space. As the
embedding need not be continuous, a quasi-geodesic does not have to be compact, nor connected, which
can be a problem. However, in a geodesic space, it is always possible to deform a quasi-geodesic
into a continuous one (at the price of worsening the quasi-isometry constants). This is the content
of the proposition \verb+quasi_geodesic_made_lipschitz+ below, which is a variation around Lemma
III.H.1.11 in~\<^cite>\<open>"bridson_haefliger"\<close>. The strategy of the proof is simple: assume that the
quasi-geodesic $c$ is defined on $[a,b]$. Then, on the points $a$, $a+C/\lambda$, $\cdots$,
$a+ N \cdot C/\lambda$, $b$, take $d$ equal to $c$, where $N$ is chosen so that the distance
between the last point and $b$ is in $[C/\lambda, 2C/\lambda)$. In the intervals, take $d$ to
be geodesic. -/
-- **Lemma 2.1**
theorem quasi_geodesic_made_lipschitz [GeodesicSpace X]
    {c : ℝ → X} {Λ : NNReal} {C a b : ℝ} (hc : QuasiIsometryOn Λ C (Icc a b) c) (hab : dist (c a) (c b) ≥ 2 * C) :
    ∃ d : ℝ → X, ContinuousOn d (Icc a b) ∧ d a = c a ∧ d b = c b
    ∧ ∀ x ∈ Icc a b, dist (c x) (d x) ≤ 4 * C
    ∧ QuasiIsometryOn Λ (4 * C) (Icc a b) d
    ∧ LipschitzOnWith (2 * Λ) d (Icc a b)
    ∧ hausdorffDist (c '' (Icc a b)) (d '' (Icc a b)) ≤ 2 * C :=
  sorry
