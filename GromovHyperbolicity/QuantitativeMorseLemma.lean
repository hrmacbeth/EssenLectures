/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD -/
import Mathlib.Data.Complex.ExponentialBounds
import GromovHyperbolicity.Prereqs.QuasiIsometry
import GromovHyperbolicity.QuasiconvexProjectionExpContracting

open Set Metric Real Classical

/-! # The Morse-Gromov Theorem

The goal of this file is to prove a central basic result in the theory of hyperbolic spaces,
usually called the Morse Lemma. It is really
a theorem, and we add the name Gromov the avoid the confusion with the other Morse lemma
on the existence of good coordinates for `C ^ 2` functions with non-vanishing hessian.

It states that a quasi-geodesic remains within bounded distance of a geodesic with the same
endpoints, the error depending only on `δ` and on the parameters $(Λ, C)$ of the
quasi-geodesic, but not on its length.

There are several proofs of this result. We will follow the one of Shchur~\<^cite> "shchur", which
gets an optimal dependency in terms of the parameters of the quasi-isometry, contrary to all
previous proofs. The price to pay is that the proof is more involved (relying in particular on
the fact that the closest point projection on quasi-convex sets is exponentially contracting).

We will also give afterwards (in a separate file)
for completeness the proof in~\<^cite> "bridson_haefliger", as it brings
up interesting tools, although the dependency it gives is worse. -/

variable {X : Type*} [MetricSpace X] [Gromov_hyperbolic_space X] [GeodesicSpace X]

open Gromov_hyperbolic_space

set_option maxHeartbeats 500000 in
/-- The next statement is the main step in the proof of the Morse-Gromov theorem given by Shchur
in~\<^cite>\<open>"shchur"\<close>, asserting that a quasi-geodesic and a geodesic with the same endpoints are close.
We show that a point on the quasi-geodesic is close to the geodesic -- the other inequality will
follow easily later on. We also assume that the quasi-geodesic is parameterized by a Lipschitz map
-- the general case will follow as any quasi-geodesic can be approximated by a Lipschitz map with
good controls.

Here is a sketch of the proof. Fix two large constants `L ≤ D` (that we will choose carefully
to optimize the values of the constants at the end of the proof). Consider a quasi-geodesic `f`
between two points $f(u^-)$ and $f(u^+)$, and a geodesic segment `G` between the same points.
Fix `f z`. We want to find a bound on `dist (f z) G`.
1 - If this distance is smaller than `L`, we are done (and the bound is `L`).
2 - Assume it is larger.
Let `pi_z` be a projection of `f z` on `G` (at distance `dist (f z) G` of `f z`), and `H` a geodesic
between `z` and `pi_z`. The idea will be to project the image of `f` on `H`, and record how much
progress is made towards `f z`. In this proof, we will construct several points before and after
`z`. When necessary, we put an exponent $-$ on the points before `z`, and `+` on the points after
`z`. To ease the reading, the points are ordered following the alphabetical order, i.e.,
`u^- ≤ v ≤ w ≤ x ≤ y^- ≤ z`.

One can find two points $f(y^-)$ and $f(y^+)$ on the left and the right of `f z` that project
on `H` roughly at distance `L` of `pi_z` (up to some $O(δ)$ -- recall that the closest point
projection is not uniquely defined, and not continuous, so we make some choice here).
Let $d^-$ be the minimal distance of $f([u^-, y^-])$ to $H$, and let $d^+$ be the minimal distance
of $f([y^+, u^+)]$ to $H$.

2.1 If the two distances $d^-$ and $d^+$ are less than `D`, then the distance between two points
realizing the minimum (say $f(c^-)$ and $f(c^+)$) is at most `2 * D + L`, hence $c^+ - c^-$ is controlled
(by `Λ * (2 * D + L) + C`) thanks to the quasi-isometry property. Therefore, `f z` is not far
away from $f(c^-)$ and $f(c^+)$ (again by the quasi-isometry property). Since the distance from
these points to `pi_z` is controlled (by `D + L`), we get a good control on `dist (f z) pi_z`, as
desired.

2.2 The interesting case is when $d^-$ and $d^+$ are both > `D`. Assume also for instance $d^- \geq
d^+$, as the other case is analogous. We will construct two points `f v` and `f x` with
`u^- ≤ v ≤ x ≤ y^-` with the following property:
\begin{equation}
\label{eq:xvK}
  K₁ e^{K₂ d(f(v), H)} \leq x-v,
\end{equation}
where `K₁` and `K₂` are some explicit constants (depending on `Λ`, `δ`, `L` and `D`).
Let us show how this will conclude the proof. The distance from `f v` to $f(c^+)$ is at most
$d(f(v),H) + L + d^+ \leq 3 d(f(v), H)$. Therefore, $c^+ - v$ is also controlled by $K' d(f(v), H)$
by the quasi-isometry property. This gives
\begin{align*}
  K &\leq K (x - v) e^{-K (c^+ - v)} \leq (e^{K (x-v)} - 1) \cdot e^{-K(c^+ - v)}
    \\& = e^{-K (c^+ - x)} - e^{-K (c^+ - v)}
    \leq e^{-K(c^+ - x)} - e^{-K (u^+ - u^-)}.
\end{align*}
This shows that, when one goes from the original quasi-geodesic $f([u^-, u^+])$ to the restricted
quasi-geodesic $f([x, c^+])$, the quantity $e^{-K \cdot}$ decreases by a fixed amount. In particular,
this process can only happen a uniformly bounded number of times, say `n`.

Let `G'` be a geodesic between `f x` and $f(c^+)$. One checks geometrically that $d(f(z), G) \leq
d(f(z), G') + (L + O(\delta))$, as both projections of `f x` and $f(c^+)$ on $H$ are within
distance $L$ of $\pi_z$. Iterating the process `n` times, one gets finally $d(f(z), G) \leq O(1) + n
(L + O(\delta))$. This is the desired bound for `dist (f z) G`.

To complete the proof, it remains to construct the points `f v` and `f x` satisfying~\eqref{eq:xvK}.
This will be done through an inductive process.

Assume first that there is a point `f v` whose projection on `H` is close to the projection of
$f(u^-)$, and with `dist (f v) H ≤ 2 d^-`. Then the projections of `f v` and $f(y^-)$ are far away
(at distance at least $L + O(\delta)$). Since the portion of `f` between `v` and $y^-$ is everywhere
at distance at least $d^-$ of `H`, the projection on `H` contracts by a factor $e^{-d^-}$. It
follows that this portion of `f` has length at least $e^{d^-} \cdot (L+O(\delta))$. Therefore, by
the quasi-isometry property, one gets $x - v \geq K e^{d^-}$. On the other hand, `dist v H` is
bounded above by $2 d^-$ by assumption. This gives the desired inequality~\eqref{eq:xvK} with $x =
y^-$.

Otherwise, all points `f v` whose projection on `H` is close to the projection of $f(u^-)$ are such
that $d(f(v), H) \geq 2 d^-$. Consider `f w₁` a point whose projection on `H` is at distance
roughly `10 * δ` of the projection of $f(u^-)$. Let `V₁` be the set of points at distance at
most $d^-$ of `H`, i.e., the $d_1$-neighborhood of `H`. Then the distance between the projections of
$f(u^-)$ and `f w₁` on `V₁` is very large (are there is an additional big contraction to go from
`V₁` to `H`). And moreover all the intermediate points `f v` are at distance at least $2 d^-$ of
`H`, and therefore at distance at least $d^-$ of `H`. Then one can play the same game as in the
first case, where $y^-$ replaced by `w₁` and `H` replaced by `V₁`. If there is a point `f v`
whose projection on `V₁` is close to the projection of $f(u^-)$, then the pair of points `v` and
`x = w₁` works. Otherwise, one lifts everything to `V₂`, the neighborhood of size $2d^-$ of `V₁`,
and one argues again in the same way.

The induction goes on like this until one finds a suitable pair of points. The process has indeed to
stop at one time, as it can only go on while $f(u^-)$ is outside of `V k`, the $(2^k-1) d^-$
neighborhood of `H`). This concludes the sketch of the proof, modulo the adjustment of constants.

Comments on the formalization below:
* The proof is written as an induction on $u^+ - u^-$. This makes it possible to either prove the
  bound directly (in the cases 1 and 2.1 above), or to use the bound on $d(z, G')$ in case 2.2
  using the induction assumption, and conclude the proof. Of course, $u^+ - u^-$ is not
  integer-valued, but in the reduction to `G'` it decays by a fixed amount, so one can easily write
  this down as a genuine induction.
* The main difficulty in the proof is to construct the pair `(v, x)` in case 2.2. This is again
  written as an induction over `k`: either the required bound is true, or one can find a point `f w`
  whose projection on `V k` is far enough from the projection of $f(u^-)$. Then, either one can use
  this point to prove the bound, or one can construct a point with the same property with respect to
  `V (k+1)`, concluding the induction.
* Instead of writing $u^-$ and $u^+$ (which are not good variable names in Isabelle), we write
  `um` and `uM`. Similarly for other variables.
* The proof only works when `δ > 0` (as one needs to divide by `δ` in the exponential gain).
  Hence, we formulate it for some `δ` which is
  strictly larger than the hyperbolicity constant. In a subsequent application of
  the lemma, we will deduce the same statement for the hyperbolicity constant
  by a limiting argument.
* To optimize the value of the constant in the end, there is an additional important trick with
  respect to the above sketch: in case 2.2, there is an exponential gain. One can spare a fraction
  `(1 - α)` of this gain to improve the constants, and spend the remaining fraction `α` to
  make the argument work. This makes it possible to reduce the value of the constant roughly from
  `40000` to `100`, so we do it in the proof below. The values of `L`, `D` and `α` can be chosen
  freely, and have been chosen to get the best possible constant in the end.
* For another optimization, we do not induct in terms of the distance from `f z` to the geodesic
  `G`, but rather in terms of the Gromov product $(f(u^-), f(u^+))_{f(z)}$ (which is the same up to
  $O(\delta)$. And we do not take for `H` a geodesic from `f z` to its projection on `G`, but rather
  a geodesic from `f z` to the point `m` on $[f(u^-), f(u^+)]$ opposite to `f z` in the tripod,
  i.e., at distance $(f(z), f(u^+))_{f(u^-)}$ of $f(u^-)$, and at distance $(f(z), f(u^-))_{f(u^+)}$
  of $f(u^+)$. Let `pi_z` denote the point on $[f(z), m]$ at distance $(f(u^-), f(u^+)_{f(z)}$ of
  `f z`. (It is within distance `2 * δ` of `m`).
  In both approaches, what we want to control by induction is the distance from `f z` to `pi_z`.
  However, in the first approach, the points $f(u^-)$ and $f(u^+)$ project on `H` between `pi_z` and
  `f z`, and since the location of their projection is only controlled up to `4 * δ` one loses
  essentially a `4 * δ`-length of `L` for the forthcoming argument. In the second approach, the
  projections on `H` are on the other side of `pi_z` compared to `f z`, so one does not lose
  anything, and in the end it gives genuinely better bounds (making it possible to gain roughly
  `10 * δ` in the final estimate). -/

/- We prove that, for any pair of points to the left and to the right of `f z`, the distance
from `f z` to a geodesic between these points is controlled. We prove this by reducing to a
closer pair of points, i.e., this is an inductive argument over real numbers. However, we
formalize it as an artificial induction over natural numbers, as this is how induction works
best, and since in our reduction step the new pair of points is always significantly closer
than the initial one, at least by an amount `δ / Λ`.

The main inductive bound that we will prove is the following. In this bound, the first term is
what comes from the trivial cases 1 and 2.1 in the description of the proof before the statement
of the theorem, while the most interesting term is the second term, corresponding to the induction
per se. -/
lemma Morse_Gromov_theorem_aux0
    {f : ℝ → X} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    {Λ C : ℝ} (hf' : quasi_isometry_on Λ C (Icc a b) f)
    (hab : a ≤ b)
    {G : Set X} (hGf : geodesic_segment_between G (f a) (f b))
    {z : ℝ} (hz : z ∈ Icc a b)
    {δ : ℝ} (hδ : δ > deltaG X)
    (n : ℕ) :
    /- We give their values to the parameters `L`, `D` and `α` that we will use in the proof.
    We also define two constants $K$ and $K_{mult}$ that appear in the precise formulation of the
    bounds. Their values have no precise meaning, they are just the outcome of the computation. -/
    let α : ℝ := 12/100
    let L : ℝ := 18 * δ
    let D : ℝ := 55 * δ
    let K : ℝ := α * log 2 / (5 * (4 + (L + 2 * δ)/D) * δ * Λ)
    let Kmult : ℝ := ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp (1/2 * log 2)) * Λ * exp (- ((1 - α) * D * log 2 / (5 * δ))) / K)
    ∀ um uM, um ∈ Icc a z → uM ∈ Icc z b
        → uM - um ≤ n * (1/4) * δ / Λ
        → Gromov_product_at (f z) (f um) (f uM)
          ≤ Λ^2 * (D + (3/2) * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (uM - um))) := by
  have hC := hf'.C_nonneg
  have := hf'.one_le_lambda
  have : Inhabited X := ⟨f 0⟩
  have hδ₀ : 0 < δ := by linarith only [hδ, delta_nonneg X]
  intro α L D K Kmult

  -- have alphaaux:"α > 0" "α ≤ 1" unfolding alpha_def by auto
  -- have "K > 0" "L > 0" "D > 0" unfolding K_def L_def D_def using \<open>δ > 0\<close> \<open>Λ ≥ 1\<close> alpha_def by auto
  -- have Laux: "L ≥ 18 * δ" "D ≥ 50 * δ" "L ≤ D" "D ≤ 4 * L" unfolding L_def D_def using \<open>δ > 0\<close> by auto
  -- have Daux: "8 * δ ≤ (1 - α) * D" unfolding alpha_def D_def using \<open>δ > 0\<close> by auto
  have : 0 < K := by ring_nf; positivity
  have : 1 ≤ Λ ^ 2 := by nlinarith only [hf'.one_le_lambda]
  have : Kmult > 0 := by ring_nf; positivity --" unfolding Kmult_def using Laux \<open>δ > 0\<close> \<open>K > 0\<close> \<open>Λ ≥ 1\<close> by (auto simp add: divide_simps)

  induction' n with n IH_n
  · -- Trivial base case of the induction
    intro um uM hum huM h_diff
    obtain ⟨rfl, rfl⟩ : z = um ∧ z = uM := by
      ring_nf at h_diff -- FIXME why doesn't `linarith` do this normalization?
      constructor <;> linarith only [h_diff, hum.2, huM.1]
    calc Gromov_product_at (f z) (f z) (f z) = 0 := by simp
      _ ≤ 1 * (D + (3/2) * L + δ + 11/2 * C) - 2 * δ + 0 * (1 - exp (- K * (z - z))) := by
        ring_nf
        positivity
      _ ≤ Λ^2 * (D + (3/2) * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (z - z))) := by
        gcongr
        simp

  intro um uM hum huM h_diff
  have : 0 ≤ uM - um := by linarith only [hum.2, huM.1]
  by_cases hz_um_uM_L : Gromov_product_at (f z) (f um) (f uM) ≤ L
  · /- If `f z` is already close to the geodesic, there is nothing to do, and we do not need
    the induction assumption. This is case 1 in the description above. -/
    calc Gromov_product_at (f z) (f um) (f uM) ≤ L := hz_um_uM_L
      _ ≤ 1 * (D + (3/2) * L + δ + 11/2 * C) - 2 * δ + 0 * (1 - exp (- K * (uM - um))) := by
        dsimp [L, D]
        linarith only [hf'.C_nonneg, hδ₀]
      _ ≤ Λ^2 * (D + (3/2) * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (uM - um))) := by
        gcongr
        have : 0 ≤ K * (uM - um) := by positivity
        simpa using this

  /- We come to the interesting case where `f z` is far away from a geodesic between
  `f um` and `f uM`. Let `m` be close to a projection of `f z` on such a geodesic (we use
  the opposite point of `f z` on the corresponding tripod). On a geodesic between `f z` and `m`,
  consider the point `pi_z` at distance $(f(um), f(uM))_{f(z)}$ of `f z`. It is very close to
  `m` (within distance `2 * δ`). We will push the points `f um` and `f uM`
  towards `f z` by considering points whose projection on a geodesic `H` between `m` and
  `z` is roughly at distance `L` of `pi_z`. -/
  let m := geodesic_segment_param {(f um)‒(f uM)} (f um) (Gromov_product_at (f um) (f z) (f uM))
  have : dist (f z) m ≤ Gromov_product_at (f z) (f um) (f uM) + 2 * deltaG X := by
    apply dist_triangle_side_middle
    exact (some_geodesic_is_geodesic_segment _ _).1
  have h_fz_m : dist (f z) m ≤ Gromov_product_at (f z) (f um) (f uM) + 2 * δ := by -- `*`
    linarith only [this, hδ]
  have H'' := -- `**`
  calc Gromov_product_at (f z) (f um) (f uM) ≤ infDist (f z) {(f um)‒(f uM)} := by
        apply Gromov_product_le_infDist
        exact (some_geodesic_is_geodesic_segment _ _).1
    _ ≤ dist (f z) m := by
        apply infDist_le_dist_of_mem
        apply geodesic_segment_param_in_geodesic_spaces3
        simp

  let H : Set X := {(f z)‒m}
  let pi_z := geodesic_segment_param H (f z) (Gromov_product_at (f z) (f um) (f uM))
  have h_H' : pi_z ∈ H ∧ m ∈ H ∧ f z ∈ H := by
    simp only [some_geodesic_endpoints, and_self, and_true, pi_z, H]
    apply geodesic_segment_param_in_segment
    exact some_geodesic_endpoints.2.2
  have h_H : geodesic_segment_between H (f z) m := by
    dsimp [H]
    exact (some_geodesic_is_geodesic_segment _ _).1
  have Dpi_z : dist (f z) pi_z = Gromov_product_at (f z) (f um) (f uM) := by
    dsimp [pi_z, H]
    apply geodesic_segment_param6 h_H
    exact ⟨Gromov_product_nonneg (f z) (f um) (f uM), H''⟩
  have : dist (f z) m = dist (f z) pi_z + dist pi_z m := (geodesic_segment_dist h_H h_H'.1).symm
  have h_pi_z_m : dist pi_z m ≤ 2 * δ := by linarith only [this, Dpi_z, h_fz_m]

  -- Introduce the notation `p` for some projection on the geodesic `H`.
  have H_nonempty (r : ℝ) : (proj_set (f r) H).Nonempty := proj_set_nonempty_of_compact
    (geodesic_segment_topology ⟨_, _, h_H⟩).1 (geodesic_segment_topology ⟨_, _, h_H⟩).2.2.2.2.2 _
  choose p hp using H_nonempty
  have pH (r : ℝ) : p r ∈ H := (hp r).1
  have pz : p z = f z := by simpa [distproj_self h_H'.2.2] using hp z

  /- The projection of `f um` on `H` is close to `pi_z` (but it does not have to be exactly
  `pi_z`). It is between `pi_z` and `m`. -/
  have := calc dist (f um) (f z) ≤ dist (f um) (p um) + dist (p um) (f z) := dist_triangle ..
    _ ≤ dist (f um) m + dist (p um) (f z) := by
      gcongr
      exact proj_set_dist_le h_H'.2.1 (hp um)
    _ = Gromov_product_at (f um) (f z) (f uM) + dist (p um) (f z) := by
      simp [m]
      apply geodesic_segment_param_in_geodesic_spaces6
      refine ⟨Gromov_product_nonneg (f um) (f z) (f uM), ?_⟩ -- TODO positivity extension
      exact (Gromov_product_le_dist _ _ _).2
  have A : Gromov_product_at (f z) (f um) (f uM) ≤ dist (p um) (f z) := by
    dsimp [Gromov_product_at] at this ⊢
    simp only [dist_comm] at this ⊢
    linarith only [this]
  -- On `H`, the point `pi_z` lies between `p um` and `f z`
  have Dum : dist (p um) (f z) = dist (p um) pi_z + dist pi_z (f z) := by
    apply le_antisymm
    · exact dist_triangle ..
    · have :=
      calc dist (p um) pi_z = |dist (p um) (f z) - dist pi_z (f z)| :=
            dist_along_geodesic_wrt_endpoint h_H (pH _) h_H'.1
        _ = dist (p um) (f z) - dist pi_z (f z) := by
          simp only [dist_comm] at Dpi_z A ⊢
          rw [Dpi_z, abs_of_nonneg]
          linarith only [A]
      linarith only [this]

  -- Choose a point `f ym` whose projection on `H` is roughly at distance `L` of `pi_z`.
  obtain ⟨ym, hym⟩ : ∃ ym ∈ Icc um z,
      (dist (p um) (p ym) ∈ Icc ((L + dist pi_z (p um)) - 4 * δ - 2 * 0) (L + dist pi_z (p um)))
                    ∧ (∀ r ∈ Icc um ym, dist (p um) (p r) ≤ L + dist pi_z (p um)) := by
    refine quasi_convex_projection_small_gaps (f := f) (G := H) ?_ hum.2 ?_ (fun t ht ↦ hp t) hδ ?_
    · exact hf.mono (Icc_subset_Icc hum.1 hz.2)
    · apply quasiconvex_of_geodesic
      exact ⟨_, _, h_H⟩
    · refine ⟨?_, ?_⟩
      · dsimp [L]
        linarith only [hδ₀, @dist_nonneg _ _ pi_z (p um)]
      · simp only [dist_comm, pz] at Dum Dpi_z hz_um_uM_L ⊢
        linarith only [Dum, hz_um_uM_L, Dpi_z]
  have h_um_ym_subset : Icc um ym ⊆ Icc a b := Icc_subset_Icc hum.1 (hym.1.2.trans hz.2)
  have : ContinuousOn (fun r ↦ infDist (f r) H) (Icc um ym) :=
    continuous_infDist_pt H |>.comp_continuousOn (hf.mono h_um_ym_subset)

  /- Choose a point `cm` between `f um` and `f ym` realizing the minimal distance to `H`.
  Call this distance `dm`. -/
  obtain ⟨closestm, hclosestm⟩ :
      ∃ closestm ∈ Icc um ym, ∀ v ∈ Icc um ym, infDist (f closestm) H ≤ infDist (f v) H := by
    refine IsCompact.exists_isMinOn ?_ ?_ this
    · exact isCompact_Icc
    · rw [nonempty_Icc]
      exact hym.1.1
  let dm : ℝ := infDist (f closestm) H
  have dm_nonneg : 0 ≤ dm := infDist_nonneg

  -- Same things but in the interval $[z, uM]$.
  have I : dist (f um) m + dist m (f uM) = dist (f um) (f uM)
            ∧ dist (f um) m = Gromov_product_at (f um) (f z) (f uM) := by
    constructor
    · apply geodesic_segment_dist (some_geodesic_is_geodesic_segment (f um) (f uM)).1
      apply geodesic_segment_param_in_geodesic_spaces3
      simp
    · apply geodesic_segment_param6
      refine (some_geodesic_is_geodesic_segment _ _).1
      simp
  have := calc dist (f uM) (f z) ≤ dist (f uM) (p uM) + dist (p uM) (f z) := dist_triangle ..
    _ ≤ dist (f uM) m + dist (p uM) (f z) := by
      gcongr
      exact proj_set_dist_le h_H'.2.1 (hp uM)
    _ = Gromov_product_at (f uM) (f z) (f um) + dist (p uM) (f z) := by
      have h₁ := Gromov_product_add (f um) (f uM) (f z)
      have h₂ := I.1
      have h₃ := I.2
      simp only [dist_comm, Gromov_product_commute] at h₁ h₂ h₃ ⊢
      linarith only [h₁, h₂, h₃]
  have A : Gromov_product_at (f z) (f um) (f uM) ≤ dist (p uM) (f z) := by
    dsimp [Gromov_product_at] at this ⊢
    simp only [dist_comm] at this ⊢
    linarith only [this]
  -- On `H`, the point `pi_z` lies between `p uM` and `f z`
  have DuM : dist (p uM) (f z) = dist (p uM) pi_z + dist pi_z (f z) := by
    apply le_antisymm
    · exact dist_triangle ..
    · have :=
      calc dist (p uM) pi_z = |dist (p uM) (f z) - dist pi_z (f z)| :=
            dist_along_geodesic_wrt_endpoint h_H (pH _) h_H'.1
        _ = dist (p uM) (f z) - dist pi_z (f z) := by
          simp only [dist_comm] at Dpi_z A ⊢
          rw [Dpi_z, abs_of_nonneg]
          linarith only [A]
      linarith only [this]

  -- Choose a point `f yM` whose projection on `H` is roughly at distance `L` of `pi_z`.
  obtain ⟨yM, hyM⟩ : ∃ yM ∈ Icc z uM,
      (dist (p uM) (p yM) ∈ Icc ((L + dist pi_z (p uM)) - 4 * δ - 2 * 0) (L + dist pi_z (p uM)))
                    ∧ (∀ r ∈ Icc yM uM, dist (p uM) (p r) ≤ L + dist pi_z (p uM)) := by
    refine quasi_convex_projection_small_gaps' (f := f) (G := H) ?_ huM.1 ?_ (fun t ht ↦ hp t) hδ ?_
    · exact hf.mono (Icc_subset_Icc hz.1 huM.2)
    · apply quasiconvex_of_geodesic
      exact ⟨_, _, h_H⟩
    · refine ⟨?_, ?_⟩
      · dsimp [L]
        linarith only [hδ₀, @dist_nonneg _ _ pi_z (p uM)]
      · simp only [dist_comm, pz] at DuM Dpi_z hz_um_uM_L ⊢
        linarith only [DuM, hz_um_uM_L, Dpi_z]
  have h_uM_yM_subset : Icc yM uM ⊆ Icc a b := Icc_subset_Icc (hz.1.trans hyM.1.1) huM.2
  have : ContinuousOn (fun r ↦ infDist (f r) H) (Icc yM uM) :=
    continuous_infDist_pt H |>.comp_continuousOn (hf.mono h_uM_yM_subset)

  /- Choose a point `cM` between `f uM` and `f yM` realizing the minimal distance to `H`.
  Call this distance `dm`. -/
  obtain ⟨closestM, hclosestM⟩ :
      ∃ closestM ∈ Icc yM uM, ∀ v ∈ Icc yM uM, infDist (f closestM) H ≤ infDist (f v) H := by
    refine IsCompact.exists_isMinOn ?_ ?_ this
    · exact isCompact_Icc
    · rw [nonempty_Icc]
      exact hyM.1.2
  let dM : ℝ := infDist (f closestM) H
  have : 0 ≤ dM := infDist_nonneg

  /- Points between `f um` and `f ym`, or between `f yM` and `f uM`, project within
  distance at most `L` of `pi_z` by construction. -/
  have P0 {x : ℝ} (hx : x ∈ Icc um ym ∪ Icc yM uM) : dist m (p x) ≤ dist m pi_z + L := by
    have h₁ := geodesic_segment_dist h_H h_H'.1
    obtain hx | hx := hx
    · have h₂ := geodesic_segment_dist h_H (pH um)
      have h₃ := hym.2.2 x hx
      have h₄ := dist_triangle m (p um) (p x)
      simp only [dist_comm] at Dum h₁ h₂ h₃ h₄ ⊢
      linarith only [Dum, h₁, h₂, h₃, h₄]
    · have h₂ := geodesic_segment_dist h_H (pH uM)
      have h₃ := hyM.2.2 x hx
      have h₄ := dist_triangle m (p uM) (p x)
      simp only [dist_comm] at DuM h₁ h₂ h₃ h₄ ⊢
      linarith only [DuM, h₁, h₂, h₃, h₄]
  have P {x : ℝ} (hx : x ∈ Icc um ym ∪ Icc yM uM) : dist pi_z (p x) ≤ L := by
    -- case-split according to whether `p x` lies (1) between `m` and `pi_z` or (2) beyond `pi_z`
    by_cases h_m_px_pi_z : dist m (p x) ≤ dist pi_z m
    · have h₁ := dist_triangle pi_z m (p x)
      simp only [dist_comm, L] at h_m_px_pi_z h_pi_z_m h₁ ⊢
      linarith only [h_pi_z_m, h_m_px_pi_z, hδ₀, h₁]
    · have h₁ := P0 hx
      have h₂ :=
      calc dist pi_z (p x) = |dist pi_z m - dist (p x) m| := by
            rw [geodesic_segment_commute] at h_H
            exact dist_along_geodesic_wrt_endpoint h_H h_H'.1 (pH _)
        _ = dist (p x) m - dist pi_z m := by
            rw [abs_of_nonpos]
            · ring
            simp only [dist_comm] at h_m_px_pi_z ⊢
            linarith only [h_m_px_pi_z]
      simp only [dist_comm] at h₁ h₂ ⊢
      linarith only [h₁, h₂]

  /- Auxiliary fact for later use:
  The distance between two points in $[um, ym]$ and $[yM, uM]$ can be controlled using
  the distances of their images under `f` to `H`, thanks to the quasi-isometry property. -/
  have hD {rm rM} (hrm : rm ∈ Icc um ym) (hrM : rM ∈ Icc yM uM) :
      |rm - rM| ≤ Λ * (infDist (f rm) H + (L + C + 2 * δ) + infDist (f rM) H) := by
    have := -- `*`
    calc dist (p rm) (p rM) = |dist (p rm) m - dist (p rM) m| := by
          rw [geodesic_segment_commute] at h_H
          apply dist_along_geodesic_wrt_endpoint h_H (pH _) (pH _)
      _ ≤ L + dist m pi_z := by
          rw [abs_le]
          have h₁ := P0 (Or.inl hrm)
          have h₂ := P0 (Or.inr hrM)
          have h₃ := @dist_nonneg _ _ (p rm) m
          have h₄ := @dist_nonneg _ _ (p rM) m
          simp only [dist_comm] at h₁ h₂ h₃ h₄ ⊢
          constructor
          · linarith only [h₂, h₃]
          · linarith only [h₁, h₄]
    have :=
    calc (1/Λ) * |rm - rM| - C ≤ dist (f rm) (f rM) :=
          hf'.lower_bound (h_um_ym_subset hrm) (h_uM_yM_subset hrM)
      _ ≤ dist (f rm) (p rm) + dist (p rm) (p rM) + dist (p rM) (f rM) := dist_triangle4 ..
      _ ≤ infDist (f rm) H + (L + 2 * δ) + infDist (f rM) H := by
          have h₁ := (hp rm).2
          have h₂ := (hp rM).2
          simp only [dist_comm] at h₁ h₂ h_pi_z_m this ⊢
          linarith only [h₁, h₂, h_pi_z_m, this]
    calc |rm - rM| = Λ * ((1/Λ) * |rm - rM| - C) + Λ * C := by field_simp
      _ ≤ Λ * (infDist (f rm) H + (L + 2 * δ) + infDist (f rM) H) + Λ * C := by gcongr
      _ = _ := by ring

  /- Auxiliary fact for later use in the inductive argument:
  the distance from `f z` to `pi_z` is controlled by the distance from `f z` to any
  intermediate geodesic between points in $f[um, ym]$ and $f[yM, uM]$, up to a constant
  essentially given by `L`. This is a variation around Lemma 5 in~\<^cite>\<open>"shchur"\<close>. -/
  have Rec {rm rM} (hrm : rm ∈ Icc um ym) (hrM : rM ∈ Icc yM uM) :
      Gromov_product_at (f z) (f um) (f uM) ≤ Gromov_product_at (f z) (f rm) (f rM) + (L + 4 * δ) := by
    have A : dist (f z) pi_z - L - 2 * deltaG X ≤ Gromov_product_at (f z) (f rm) (p rm) := by
      have h₁ : dist (f rm) (p rm) + dist (p rm) (f z) ≤ dist (f rm) (f z) + 4 * deltaG X :=
        dist_along_geodesic ⟨_, _, h_H⟩ (hp _) h_H'.2.2
      have h₂ : dist (f z) pi_z ≤ dist (f z) (p rm) + dist (p rm) pi_z := dist_triangle ..
      have h₃ := P (Or.inl hrm)
      simp only [Gromov_product_at, dist_comm] at h₁ h₂ h₃ ⊢
      linarith only [h₁, h₂, h₃]
    have B : dist (f z) pi_z - L - 2 * deltaG X ≤ Gromov_product_at (f z) (p rM) (f rM) := by
      have h₁ : dist (f rM) (p rM) + dist (p rM) (f z) ≤ dist (f rM) (f z) + 4 * deltaG X :=
        dist_along_geodesic ⟨_, _, h_H⟩ (hp _) h_H'.2.2
      have h₂ : dist (f z) pi_z ≤ dist (f z) (p rM) + dist (p rM) pi_z := dist_triangle ..
      have h₃ := P (Or.inr hrM)
      simp only [Gromov_product_at, dist_comm] at h₁ h₂ h₃ ⊢
      linarith only [h₁, h₂, h₃]
    have C : dist (f z) pi_z - L - 2 * deltaG X ≤ Gromov_product_at (f z) (p rm) (p rM) := by
      by_cases h : dist (f z) (p rm) ≤ dist (f z) (p rM)
      · have h₁ :=
        calc dist (p rm) (p rM) = |dist (f z) (p rm) - dist (f z) (p rM)| := by
              have := dist_along_geodesic_wrt_endpoint h_H (pH rm) (pH rM)
              simp only [dist_comm] at this ⊢
              linarith only [this]
          _ = dist (f z) (p rM) - dist (f z) (p rm) := by
              rw [abs_of_nonpos]
              · ring
              · linarith only [h]
        have h₂ : dist (f z) pi_z ≤ dist (f z) (p rm) + dist (p rm) pi_z := dist_triangle ..
        have h₃ := P (Or.inl hrm)
        simp only [Gromov_product_at, dist_comm] at h h₁ h₂ h₃ ⊢
        linarith only [h, h₁, h₂, h₃, delta_nonneg X]
      · have h₁ :=
        calc dist (p rm) (p rM) = |dist (f z) (p rm) - dist (f z) (p rM)| := by
              have := dist_along_geodesic_wrt_endpoint h_H (pH rm) (pH rM)
              simp only [dist_comm] at this ⊢
              linarith only [this]
          _ = dist (f z) (p rm) - dist (f z) (p rM) := by
              rw [abs_of_nonneg]
              linarith only [h]
        have h₂ : dist (f z) pi_z ≤ dist (f z) (p rM) + dist (p rM) pi_z := dist_triangle ..
        have h₃ := P (Or.inr hrM)
        simp only [Gromov_product_at, dist_comm] at h h₁ h₂ h₃ ⊢
        linarith only [h, h₁, h₂, h₃, delta_nonneg X]
    have :=
    calc Gromov_product_at (f z) (f um) (f uM) - L - 2 * deltaG X
        ≤ min (Gromov_product_at (f z) (f rm) (p rm))
            (min (Gromov_product_at (f z) (p rm) (p rM))
              (Gromov_product_at (f z) (p rM) (f rM))) := by
          simp only [le_min_iff, ← Dpi_z]
          exact ⟨A, C, B⟩
      _ ≤ Gromov_product_at (f z) (f rm) (f rM) + 2 * deltaG X :=
            hyperb_ineq_4_points' (f z) (f rm) (p rm) (p rM) (f rM)
    linarith only [this, hδ]

  /- We have proved the basic facts we will need in the main argument. This argument starts
  here. It is divided in several cases. -/
  obtain ⟨hdm, hdM⟩ | ⟨I₁, I₂⟩ | ⟨hdM, hdmM⟩ : (dm ≤ D + 4 * C ∧ dM ≤ D + 4 * C)
      ∨ (dm ≥ D + 4 * C ∧ dM ≤ dm) ∨ (dM ≥ D + 4 * C ∧ dm ≤ dM) := by
    obtain hdm1 | hdm2 := le_or_lt dm (D + 4 * C)
    · obtain hdM1 | hdm2 := le_or_lt dM (D + 4 * C)
      · left
        exact ⟨hdm1, hdM1⟩
      · right
        right
        exact ⟨hdm2.le, hdm1.trans hdm2.le⟩
    · obtain hdmM1 | hdmM2 := le_or_lt dm dM
      · right
        right
        exact ⟨hdm2.le.trans hdmM1, hdmM1⟩
      · right
        left
        exact ⟨hdm2.le, hdmM2.le⟩

  /- Case 2.1 of the description before the statement: there are points in $f[um, ym]$ and
  in $f[yM, uM]$ which are close to `H`. Then one can conclude directly, without relying
  on the inductive argument, thanks to the quasi-isometry property. -/
  · have I : Gromov_product_at (f z) (f closestm) (f closestM) ≤ Λ^2 * (D + L / 2 + δ + 11/2 * C) - 6 * δ := by
      have H :=
      calc dist (f closestm) (f z) + dist (f z) (f (closestM))
            ≤ (Λ * |closestm - z| + C) + (Λ * |z - closestM| + C) := by
              rw [← Real.dist_eq]
              gcongr
              · exact hf'.upper_bound (h_um_ym_subset hclosestm.1) hz
              · exact hf'.upper_bound hz (h_uM_yM_subset hclosestM.1)
          _ = Λ * |closestm - closestM| + 1 * 2 * C := by
              have h₁ := hclosestm.1.2
              have h₂ := hclosestM.1.1
              have h₃ := hym.1.2
              have h₄ := hyM.1.1
              rw [abs_of_nonpos, abs_of_nonpos, abs_of_nonpos] <;> linarith only [h₁, h₂, h₃, h₄]
      by_cases h_closest : dist (f closestm) (f closestM) ≤ 12 * δ
      · have :=
        calc 2 * Gromov_product_at (f z) (f closestm) (f closestM)
            ≤ dist (f closestm) (f z) + dist (f z) (f (closestM)) := by
              dsimp [Gromov_product_at]
              have := @dist_nonneg _ _ (f closestm) (f closestM)
              simp only [dist_comm] at this ⊢
              linarith only [this]
          _ ≤ Λ * |closestm - closestM| + 1 * 2 * C := H
          _ = Λ ^ 2 * (1 / Λ * |closestm - closestM| - C) + Λ ^ 2 * C + 1 * 2 * C := by
              field_simp
              ring
          _ ≤ Λ ^ 2 * dist (f closestm) (f closestM) + Λ ^ 2 * C + 1 * 2 * C := by
              gcongr
              rw [← Real.dist_eq]
              exact hf'.lower_bound (h_um_ym_subset hclosestm.1) (h_uM_yM_subset hclosestM.1)
          _ ≤ Λ ^ 2 * (12 * δ) + Λ ^ 2 * C + Λ ^ 2 * 2 * C:= by gcongr
          _ = Λ^2 * (24 * δ + 3 * C) - Λ^2 * 12 * δ := by ring
          _ ≤ Λ^2 * ((2 * D + L + 2 * δ) + 11 * C) - 1 * 12 * δ := by
              gcongr
              . dsimp [D, L]
                linarith only [hδ₀]
              · norm_num
        linarith only [this]
      · have :=
        calc dist (f closestm) (f z) + dist (f z) (f (closestM))
            ≤ Λ * |closestm - closestM| + 1 * 2 * C := H
          _ ≤ Λ * (Λ * (dm + (L + C + 2 * δ) + dM)) + 1 * 2 * C := by
              gcongr
              exact hD hclosestm.1 hclosestM.1
          _ ≤ Λ * (Λ * ((D + 4 * C) + (L + C + 2 * δ) + (D + 4 * C))) + Λ^2 * 2 * C := by gcongr
        simp only [Gromov_product_at, dist_comm] at this h_closest ⊢
        linarith only [this, h_closest]
    calc Gromov_product_at (f z) (f um) (f uM)
        ≤ Gromov_product_at (f z) (f closestm) (f closestM) + 1 * L + 4 * δ + 0 * (1 - exp (- K * (uM - um))) := by
          convert Rec hclosestm.1 hclosestM.1 using 1
          ring
      _ ≤ (Λ^2 * (D + L / 2 + δ + 11/2 * C) - 6 * δ) + Λ^2 * L + 4 * δ + Kmult * (1 - exp (- K * (uM - um))) := by
          gcongr
          simp only [neg_mul, sub_nonneg, exp_le_one_iff, neg_le, neg_zero]
          positivity
      _ = _ := by field_simp; ring
    -- End of the easy case 2.1

  /- Case 2.2: `dm` is large, i.e., all points in $f[um, ym]$ are far away from `H`. Moreover,
  assume that `dm ≥ dM`. Then we will find a pair of points `v` and `x` with `um ≤ v ≤ x ≤ ym`
  satisfying the estimate~\eqref{eq:xvK}. We argue by induction: while we
  have not found such a pair, we can find a point `x_k` whose projection on `V_k`, the
  neighborhood of size `(2^k-1) * dm` of `H`, is far enough from the projection of `um`, and
  such that all points in between are far enough from `V_k` so that the corresponding
  projection will have good contraction properties. -/
  · have : 0 < dm := by dsimp [D] at I₁; linarith only [I₁, hC, hδ₀]
    let V : ℕ → Set X := fun k ↦ cthickening ((2^k - 1) * dm) H
    let QC : ℕ → ℝ := fun k ↦ if k = 0 then 0 else 8 * δ
    have {k : ℕ} : 0 ≤ QC k := by dsimp [QC]; split <;> positivity
    have Q (k : ℕ) : quasiconvex (0 + 8 * deltaG X) (V k) := by
      apply quasiconvex_thickening
      · apply quasiconvex_of_geodesic ⟨_, _, h_H⟩
      · have : 1 ≤ (2:ℝ) ^ k := one_le_pow_of_one_le (by norm_num) k
        have : 0 ≤ (2:ℝ) ^ k - 1 := by linarith only [this]
        positivity
    have V_quasiconvex (k : ℕ) : quasiconvex (QC k) (V k) := by
      dsimp [QC]
      split_ifs with h
      · simp only [h, pow_zero, sub_self, zero_mul, V, cthickening_zero]
        rw [IsClosed.closure_eq]
        · apply quasiconvex_of_geodesic ⟨_, _, h_H⟩
        exact (geodesic_segment_topology ⟨_, _, h_H⟩).2.2.2.2.1
      · refine quasiconvex_mono ?_ (Q k)
        linarith only [hδ]

    -- Define `q k x` to be the projection of `f x` on `V k`.
    let q : ℕ → ℝ → X := fun k x ↦ geodesic_segment_param {p x‒f x} (p x) ((2^k - 1) * dm)
    have hq0 (x : ℝ) : q 0 x = p x := by
      dsimp [q]
      convert @geodesic_segment_param_in_geodesic_spaces1 _ _ (p x) (f x)
      simp

    -- The inductive argument
    have Ind_k (k : ℕ) :
        Gromov_product_at (f z) (f um) (f uM)
          ≤ Λ^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (uM - um)))
        ∨ (∃ x ∈ Icc um ym, (∀ w ∈ Icc um x, dist (f w) (p w) ≥ (2^(k+1)-1) * dm)
            ∧ dist (q k um) (q k x) ≥ L - 4 * δ + 7 * QC k) := by
      induction' k with k IH
      /- Base case: there is a point far enough from `q 0 um` on `H`. This is just the point `ym`,
      by construction. -/
      · right
        refine ⟨ym, ?_, ?_, ?_⟩
        · simp [hym.1.1]
        · intro w hw
          calc _ = _ := by ring
            _ ≤ _ := hclosestm.2 w hw
            _ ≤ _ := infDist_le_dist_of_mem (pH _)
        · simp only [hq0, QC, reduceIte]
          have h₁ := hym.2.1.1
          have h₂ := @dist_nonneg _ _ pi_z (p um)
          simp only [dist_comm] at h₁ h₂ ⊢
          linarith only [h₁, h₂]

      /- The induction. The inductive assumption claims that, either the desired inequality
      holds, or one can construct a point with good properties. If the desired inequality holds,
      there is nothing left to prove. Otherwise, we can start from this point at step `k`,
      say `x`, and either prove the desired inequality or construct a point with the good
      properties at step `k + 1`. -/
      by_cases h :
        Gromov_product_at (f z) (f um) (f uM)
          ≤ Λ ^ 2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (uM - um)))
      · exact Or.inl h

      obtain ⟨x, hx₁, hx₂, hx₃⟩ :
        ∃ x ∈ Icc um ym, (∀ w, w ∈ Icc um x → dist (f w) (p w) ≥ (2^(k+1)-1) * dm)
          ∧ dist (q k um) (q k x) ≥ L - 4 * δ + 7 * QC k :=
        IH.resolve_left h

      -- Some auxiliary technical inequalities to be used later on.
      have aux : (2 ^ k - 1) * dm ≤ (2*2^k-1) * dm ∧ 0 ≤ 2 * 2 ^ k - (1:ℝ) ∧ dm ≤ dm * 2 ^ k := sorry
  --             apply (auto simp add: algebra_simps)
  --             apply (metis power.simps(2) two_realpow_ge_one)
  --             using \<open>0 ≤ dm\<close> less_eq_real_def by fastforce
      have aux2 : L + C + 2 * δ ≤ ((L + 2 * δ)/D) * dm := by
        have :=
        calc L + C = (L/D) * (D + (D/L) * C) := by field_simp; ring
          _ ≤ (L/D) * (D + 4 * C) := sorry
    --             apply (intro mono_intros)
    --             using \<open>L > 0\<close> \<open>D > 0\<close> \<open>C ≥ 0\<close> \<open>D ≤ 4 * L\<close> by (auto simp add: algebra_simps divide_simps)
          _ ≤ (L/D) * dm := sorry
    --             apply (intro mono_intros) using I \<open>L > 0\<close> \<open>D > 0\<close> by auto
        have : 2 * δ ≤ (2 * δ)/D * dm := sorry
    --             using I \<open>C ≥ 0\<close> \<open>δ > 0\<close> \<open>D > 0\<close> by (auto simp add: algebra_simps divide_simps)
        sorry
  --             by (auto simp add: algebra_simps divide_simps)
      have aux3 : (1-α) * D + α * 2^k * dm ≤ dm * 2^k - C/2 - QC k := by
        dsimp [QC]
        split_ifs with h
        · simp [h]
  --                using I \<open>C ≥ 0\<close> unfolding True QC_def alpha_def by auto
          sorry
        have :=
        calc C/2 + 8 * δ + (1-α) * D ≤ 2 * (1-α) * dm := sorry
  --               using I \<open>C ≥ 0\<close> unfolding QC_def alpha_def using False Laux by auto
          _ ≤ 2^k * (1-α) * dm := sorry
  --               apply (intro mono_intros) using False alphaaux I \<open>D > 0\<close> \<open>C ≥ 0\<close> by auto
        linarith only [this]

      /- Construct a point `w` such that its projection on `V k` is close to that of `um`
      and therefore far away from that of `x`. This is just the intermediate value theorem
      (with some care as the closest point projection is not continuous). -/
      obtain ⟨w, hw₁, hw₂, hw₃⟩ : ∃ w ∈ Icc um x,
          dist (q k um) (q k w) ∈ Icc ((9 * δ + 4 * QC k) - 4 * δ - 2 * QC k) (9 * δ + 4 * QC k)
          ∧ (∀ v ∈ Icc um w, dist (q k um) (q k v) ≤ 9 * δ + 4 * QC k) := by
        apply quasi_convex_projection_small_gaps (f := f) (G := V k) <;> sorry
  --             show "continuous_on {um..x} f"
  --               apply (rule continuous_on_subset[OF \<open>continuous_on Icc a b f\<close>])
  --               using \<open>um ∈ {a..z}\<close> \<open>z ∈ Icc a b\<close> \<open>ym ∈ {um..z}\<close> \<open>x ∈ {um..ym}\<close> by auto
  --             show "um ≤ x" using \<open>x ∈ {um..ym}\<close> by auto
  --             show "quasiconvex (QC k) (V k)" by fact
  --             show "deltaG TYPE('a) < δ" by fact
  --             show "9 * δ + 4 * QC k ∈ {4 * δ + 2 * QC k..dist (q k um) (q k x)}"
  --               using x(2) \<open>δ > 0\<close> \<open>QC k ≥ 0\<close> Laux by auto
  --             show "q k w ∈ proj_set (f w) (V k)" if "w ∈ {um..x}" for w
  --               unfolding V_def q_def apply (rule proj_set_thickening)
  --               using aux p x(3)[OF that] by (auto simp add: metric_space_class.dist_commute)
  --           qed

      /- There are now two cases to be considered: either one can find a point `v` between
      `um` and `w` which is close enough to `H`. Then this point will satisfy~\eqref{eq:xvK},
      and we will be able to prove the desired inequality. Or there is no such point,
      and then `w` will have the good properties at step `k+1` -/
      by_cases h : ∃ v ∈ Icc um w, dist (f v) (p v) ≤ (2^(k+2)-1) * dm
      /- First subcase: there is a good point `v` between `um` and `w`. This is the
      heart of the argument: we will show that the desired inequality holds. -/
      · left
        obtain ⟨v, hv₁, hv₂⟩ := h
        -- Auxiliary basic fact to be used later on.
        have aux4 {r : ℝ} (hr : r ∈ Icc v x) : dm * 2 ^ k ≤ infDist (f r) (V k) := by
  --               have *: "q k r ∈ proj_set (f r) (V k)"
  --                 unfolding q_def V_def apply (rule proj_set_thickening)
  --                 using aux p[of r] x(3)[of r] that \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> by (auto simp add: metric_space_class.dist_commute)
  --               have := calc infDist (f r) (V k) = dist (geodesic_segment_param {p r‒f r} (p r) (dist (p r) (f r))) (geodesic_segment_param {p r‒f r} (p r) ((2 ^ k - 1) * dm))"
  --                 using proj_setD(2)[OF *] unfolding q_def by auto
  --               _ = abs(dist (p r) (f r) - (2 ^ k - 1) * dm)"
  --                 apply (rule geodesic_segment_param(7)[where ?y = "f r"])
  --                 using x(3)[of r] \<open>r ∈ {v..x}\<close> \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> aux by (auto simp add: metric_space_class.dist_commute)
  --               _ = dist (f r) (p r) - (2 ^ k - 1) * dm"
  --                 using x(3)[of r] \<open>r ∈ {v..x}\<close> \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> aux by (auto simp add: metric_space_class.dist_commute)
  --               finally have "dist (f r) (p r) = infDist (f r) (V k) + (2 ^ k - 1) * dm" by simp
  --               moreover have "(2^(k+1) - 1) * dm ≤ dist (f r) (p r)"
  --                 apply (rule x(3)) using \<open>r ∈ {v..x}\<close> \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> by auto
  --               ultimately have "(2^(k+1) - 1) * dm ≤ infDist (f r) (V k) + (2 ^ k - 1) * dm"
  --                 by simp
  --               then show ?thesis by (auto simp add: algebra_simps)
  --             qed
          sorry

        /- Substep 1: We can control the distance from `f v` to `f closestM` in terms of the distance
        of the distance of `f v` to `H`, i.e., by `2^k * dm`. The same control follows
        for `closestM - v` thanks to the quasi-isometry property. Then, we massage this
        inequality to put it in the form we will need, as an upper bound on `(x-v) * exp (-2^k * dm)`. -/
        have : infDist (f v) H ≤ (2^(k+2)-1) * dm := sorry
  --               using v proj_setD(2)[OF p[of v]] by auto
        have :=
        calc |v - closestM| ≤ Λ * (infDist (f v) H + (L + C + 2 * δ) + infDist (f closestM) H) := sorry
  --               apply (rule D)
  --               using \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> \<open>x ∈ {um..ym}\<close> \<open>ym ∈ {um..z}\<close> \<open>um ∈ {a..z}\<close> \<open>z ∈ Icc a b\<close> \<open>closestM ∈ {yM..uM}\<close> \<open>yM ∈ {z..uM}\<close> \<open>uM ∈ {z..b}\<close> by auto
          _ ≤ Λ * ((2^(k+2)-1) * dm + (L + C + 2 * δ) + dM) := by gcongr
          _ = Λ * ((2^(k+2)-1) * dm + 1 * (L + C + 2 * δ) + dM) := by ring
          _ ≤ Λ * ((2^(k+2)-1) * dm + 2^k * (((L + 2 * δ)/D) * dm) + dm) := by
              gcongr
              apply one_le_pow_of_one_le
              norm_num
          _ = Λ * 2^k * (4 + (L + 2 * δ)/D) * dm := by ring
        have : |v - closestM| / (Λ * (4 + (L + 2 * δ)/D)) ≤ 2^k * dm := sorry -- `*`
  --               using \<open>Λ ≥ 1\<close> \<open>L > 0\<close> \<open>D > 0\<close> \<open>δ > 0\<close> by (simp add: divide_simps, simp add: algebra_simps)
        /- We reformulate this control inside of an exponential, as this is the form we
        will use later on. -/
        have :=
        calc exp (- (α * (2^k * dm) * log 2 / (5 * δ)))
            ≤ exp (-(α * (|v - closestM| / (Λ * (4 + (L + 2 * δ)/D))) * log 2 / (5 * δ))) := by
              gcongr
          _ = exp (-K * |v - closestM|) := by
              dsimp [K]
              congr
              field_simp
              ring
          _ = exp (-K * (closestM - v)) := by
              congr
              rw [abs_of_nonpos]
              · ring
              sorry
  --               unfolding dist_real_def using \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> \<open>x ∈ {um..ym}\<close> \<open>ym ∈ {um..z}\<close> \<open>yM ∈ {z..uM}\<close> \<open>closestM ∈ {yM..uM}\<close> \<open>K > 0\<close> by auto
        have : 0 ≤ x - v := sorry
        -- Plug in `x-v` to get the final form of this inequality.
        have :=
        calc K * (x - v) * exp (- (α * (2^k * dm) * log 2 / (5 * δ)))
            ≤ K * (x - v) * exp (-K * (closestM - v)) := by gcongr
          _ = ((K * (x - v) + 1) - 1) * exp (- K * (closestM - v)) := by ring
          _ ≤ (exp (K * (x - v)) - 1) * exp (-K * (closestM - v)) := by gcongr; apply add_one_le_exp
          _ = exp (-K * (closestM - x)) - exp (-K * (closestM - v)) := by
              rw [sub_mul, ← exp_add]
              ring_nf
          _ ≤ exp (-K * (closestM - x)) - exp (-K * (uM - um)) := by
              gcongr _ - exp ?_
              apply mul_le_mul_of_nonpos_left
              · sorry
  --               using \<open>K > 0\<close> \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> \<open>x ∈ {um..ym}\<close> \<open>ym ∈ {um..z}\<close> \<open>yM ∈ {z..uM}\<close> \<open>closestM ∈ {yM..uM}\<close> by auto
              rw [Left.neg_nonpos_iff]
              positivity
        have B : (x - v) * exp (- (α * (2^k * dm) * log 2 / (5 * δ)))
            ≤ (exp (-K * (closestM - x)) - exp (-K * (uM-um)))/K := by
          rw [le_div_iff]
          · convert this using 1
            ring
          positivity
        -- End of substep 1

        /- Substep 2: The projections of `f v` and `f x` on the cylinder `V k` are well separated,
        by construction. This implies that `v` and `x` themselves are well separated, thanks
        to the exponential contraction property of the projection on the quasi-convex set `V k`.
        This leads to a uniform lower bound for `(x-v) * exp (-2^k * dm)`, which has been upper bounded
        in Substep 1. -/
        have :=
        calc L - 4 * δ + 7 * QC k ≤ dist (q k um) (q k x) := hx₃
          _ ≤ dist (q k um) (q k v) + dist (q k v) (q k x) := dist_triangle ..
          _ ≤ (9 * δ + 4 * QC k) + dist (q k v) (q k x) := by
              gcongr
              apply hw₃ _ hv₁
        have :=
        calc L - 13 * δ + 3 * QC k ≤ dist (q k v) (q k x) := by linarith only [this]
          _ ≤ 3 * QC k + max (5 * deltaG X)
                ((4 * exp (1/2 * log 2)) * Λ * (x - v)
                * exp (-(dm * 2^k - C/2 - QC k) * log 2 / (5 * δ))) := by
              /- We use different statements for the projection in the case `k = 0` (projection on
              a geodesic) and `k > 0` (projection on a quasi-convex set) as the bounds are better in
              the first case, which is the most important one for the final value of the constant. -/
              obtain rfl | hk := Nat.eq_zero_or_pos k
              ·
                have : dist (q 0 v) (q 0 x)
                    ≤ max (5 * deltaG X)
                      ((4 * exp (1/2 * log 2)) * Λ * (x - v) * exp (-(dm * 2^0 - C/2) * log 2 / (5 * δ))) := sorry
        --               proof (rule geodesic_projection_exp_contracting[where ?G = "V k" and ?f = f])
        --                 show "geodesic_segment (V k)" unfolding True V_def using geodesic_segmentI[OF H] by auto
        --                 show "v ≤ x" using \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> by auto
        --                 show "q k v ∈ proj_set (f v) (V k)"
        --                   unfolding q_def V_def apply (rule proj_set_thickening)
        --                   using aux p[of v] x(3)[of v] \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> by (auto simp add: metric_space_class.dist_commute)
        --                 show "q k x ∈ proj_set (f x) (V k)"
        --                   unfolding q_def V_def apply (rule proj_set_thickening)
        --                   using aux p[of x] x(3)[of x] \<open>w ∈ {um..x}\<close> by (auto simp add: metric_space_class.dist_commute)
        --                 show "15/2 * δ + C/2 ≤ dm * 2^k"
        --                   apply (rule order_trans[of _ dm])
        --                   using I \<open>δ > 0\<close> \<open>C ≥ 0\<close> Laux unfolding QC_def by auto
        --                 show "deltaG TYPE('a) < δ" by fact
        --                 show "∀ t. t ∈ {v..x} → dm * 2 ^ k ≤ infDist (f t) (V k)"
        --                   using aux4 by auto
        --                 show "0 ≤ C" "0 ≤ Λ" using \<open>C ≥ 0\<close> \<open>Λ ≥ 1\<close> by auto
        --                 show "dist (f x1) (f x2) ≤ Λ * dist x1 x2 + C" if "x1 ∈ {v..x}" "x2 ∈ {v..x}" for x1 x2
        --                   using quasi_isometry_onD(1)[OF assms(2)] that \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> \<open>x ∈ {um..ym}\<close> \<open>ym ∈ {um..z}\<close> \<open>um ∈ {a..z}\<close> \<open>z ∈ Icc a b\<close> by auto
        --               qed
                simp only [hq0] at this ⊢
        --               then show ?thesis unfolding QC_def True by auto
                sorry
              ·
        --             next
        --               case False
        --               have "dist (q k v) (q k x) ≤ 2 * QC k + 8 * δ + max (5 * deltaG X) ((4 * exp(1/2 * log 2)) * Λ * (x - v) * exp(-(dm * 2^k - QC k -C/2) * log 2 / (5 * δ)))"
        --               proof (rule quasiconvex_projection_exp_contracting[where ?G = "V k" and ?f = f])
        --                 show "quasiconvex (QC k) (V k)" by fact
        --                 show "v ≤ x" using \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> by auto
        --                 show "q k v ∈ proj_set (f v) (V k)"
        --                   unfolding q_def V_def apply (rule proj_set_thickening)
        --                   using aux p[of v] x(3)[of v] \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> by (auto simp add: metric_space_class.dist_commute)
        --                 show "q k x ∈ proj_set (f x) (V k)"
        --                   unfolding q_def V_def apply (rule proj_set_thickening)
        --                   using aux p[of x] x(3)[of x] \<open>w ∈ {um..x}\<close> by (auto simp add: metric_space_class.dist_commute)
        --                 show "15/2 * δ + QC k + C/2 ≤ dm * 2^k"
        --                   apply (rule order_trans[of _ dm])
        --                   using I \<open>δ > 0\<close> \<open>C ≥ 0\<close> Laux unfolding QC_def by auto
        --                 show "deltaG TYPE('a) < δ" by fact
        --                 show "∀ t. t ∈ {v..x} → dm * 2 ^ k ≤ infDist (f t) (V k)"
        --                   using aux4 by auto
        --                 show "0 ≤ C" "0 ≤ Λ" using \<open>C ≥ 0\<close> \<open>Λ ≥ 1\<close> by auto
        --                 show "dist (f x1) (f x2) ≤ Λ * dist x1 x2 + C" if "x1 ∈ {v..x}" "x2 ∈ {v..x}" for x1 x2
        --                   using quasi_isometry_onD(1)[OF assms(2)] that \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> \<open>x ∈ {um..ym}\<close> \<open>ym ∈ {um..z}\<close> \<open>um ∈ {a..z}\<close> \<open>z ∈ Icc a b\<close> by auto
        --               qed
        --               then show ?thesis unfolding QC_def using False by (auto simp add: algebra_simps)
        --             qed
                sorry

        have : L - 13 * δ ≤ max (5 * deltaG X)
          ((4 * exp (1/2 * log 2)) * Λ * (x - v) * exp (-(dm * 2^k - C/2 - QC k) * log 2 / (5 * δ))) := by
          linarith only [this]
        have A :=
        calc L - 13 * δ ≤ (4 * exp (1/2 * log 2)) * Λ * (x - v) * exp (-(dm * 2^k - C/2 - QC k) * log 2 / (5 * δ)) := sorry
  --               using \<open>δ > deltaG X\<close> Laux by auto
--             /- We separate the exponential gain coming from the contraction into two parts, one
--             to be spent to improve the constant, and one for the inductive argument. -/
          _ ≤ (4 * exp (1/2 * log 2)) * Λ * (x - v) * exp (-((1-α) * D + α * 2^k * dm) * log 2 / (5 * δ)) := sorry
  --               apply (intro mono_intros) using aux3 \<open>δ > 0\<close> \<open>Λ ≥ 1\<close> \<open>v ∈ {um..w}\<close> \<open>w ∈ {um..x}\<close> by auto
          _ = (4 * exp (1/2 * log 2)) * Λ * (x - v) * (exp (-(1-α) * D * log 2 / (5 * δ)) * exp (-α * 2^k * dm * log 2 / (5 * δ))) := sorry
  --               unfolding mult_exp_exp by (auto simp add: algebra_simps divide_simps)
          _ ≤ (4 * exp (1/2 * log 2)) * Λ * exp (-((1-α) * D * log 2 / (5 * δ))) * ((x - v) * exp (-(α * (2^k * dm) * log 2 / (5 * δ)))) := sorry
  --               by (simp add: algebra_simps)
        -- This is the end of the second substep.

        /- Use the second substep to show that `x-v` is bounded below, and therefore
        that `closestM - x` (the endpoints of the new geodesic we want to consider in the
        inductive argument) are quantitatively closer than `uM - um`, which means that we
        will be able to use the inductive assumption over this new geodesic. -/
        have :=
        calc L - 13 * δ
            ≤ (4 * exp (1/2 * log 2)) * Λ * exp (-((1-α) * D * log 2 / (5 * δ))) * ((x - v) * exp (-(α * (2^k * dm) * log 2 / (5 * δ)))) := A  --
          _ ≤ (4 * exp (1/2 * log 2)) * Λ * exp 0 * ((x - v) * exp 0) := by
              gcongr
              · rw [Left.neg_nonpos_iff]
                positivity
              · rw [Left.neg_nonpos_iff]
                positivity
          _ = (4 * exp (1/2 * log 2)) * Λ * (x-v) := by simp
          _ ≤ 20 * Λ * (x - v) := by
              gcongr
              -- FIXME `linarith` ought to be better at the following calculation, division bug?
              calc 4 * exp (1 / 2 * log 2) ≤ 4 * exp (1 / 2 * 0.6931471808) := by
                    gcongr
                    exact log_two_lt_d9.le
                _ ≤ 4 * exp 1 := by
                    gcongr
                    norm_num1
                _ ≤ 4 * 2.7182818286 := by
                    gcongr
                    exact exp_one_lt_d9.le
                _ ≤ 20 := by norm_num1
        have : (1/4) * δ / Λ ≤ x - v := by
          rw [div_le_iff]
          · dsimp [L] at this
            linarith only [this]
          positivity
        have :=
        calc closestM - x + (1/4) * δ / Λ
            ≤ closestM - v := by sorry --simp
          _ ≤ uM - um := sorry
  --               using \<open>closestM ∈ {yM..uM}\<close> \<open>v ∈ {um..w}\<close> by auto
          _ ≤ (n + 1) * (1/4) * δ / Λ := sorry
        have : closestM - x ≤ n * (1/4) * δ / Λ := by
          rw [← sub_nonneg] at this ⊢
          convert this using 1
          ring_nf -- FIXME why doesn't `linarith` work here?

        /- Conclusion of the proof: combine the lower bound of the second substep with
        the upper bound of the first substep to get a definite gain when one goes from
        the old geodesic to the new one. Then, apply the inductive assumption to the new one
        to conclude the desired inequality for the old one. -/
        have : 0 < (L - 13 * δ) := by
          dsimp [L]
          ring_nf
          positivity
        have :=
        calc L + 4 * δ = ((L + 4 * δ)/(L - 13 * δ)) * (L - 13 * δ) := by field_simp
          _ ≤ ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp (1/2 * log 2)) * Λ
              * exp (- ((1 - α) * D * log 2 / (5 * δ))) * ((x - v)
              * exp (- (α * (2 ^ k * dm) * log 2 / (5 * δ))))) := by gcongr
          _ ≤ ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp (1/2 * log 2)) * Λ
              * exp (- ((1 - α) * D * log 2 / (5 * δ)))
              * ((exp (-K * (closestM - x)) - exp (-K * (uM - um)))/K)) := by gcongr
          _ = Kmult * (exp (-K * (closestM - x)) - exp (-K * (uM - um))) := by
              dsimp [Kmult]
              ring

        calc Gromov_product_at (f z) (f um) (f uM)
            ≤ Gromov_product_at (f z) (f x) (f closestM) + (L + 4 * δ) := sorry
  --               apply (rule Rec) using \<open>closestM ∈ {yM..uM}\<close> \<open>x ∈ {um..ym}\<close> \<open>ym ∈ {um..z}\<close> by auto
          _ ≤ (Λ ^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ
              + Kmult * (1 - exp (- K * (closestM - x))))
              + (Kmult * (exp (-K * (closestM - x)) - exp (-K * (uM-um)))) := sorry
  --               apply (intro mono_intros C Suc.IH)
  --               using \<open>x ∈ {um..ym}\<close> \<open>ym ∈ {um..z}\<close> \<open>um ∈ {a..z}\<close> \<open>closestM ∈ {yM..uM}\<close> \<open>yM ∈ {z..uM}\<close> \<open>uM ∈ {z..b}\<close> \<open>closestM - x ≤ n * (1/4) * δ / Λ\<close> by auto
          _ = (Λ^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (uM - um)))) := by
              dsimp [K]
              ring
        -- End of the first subcase, when there is a good point `v` between `um` and `w`.

      /- Second subcase: between `um` and `w`, all points are far away from `V k`. We
      will show that this implies that `w` is admissible for the step `k+1`. -/
      · right
        push_neg at h
        refine ⟨w, ⟨hw₁.1, hw₁.2.trans hx₁.2⟩, fun x hx ↦ (h x hx).le, ?_⟩
        have h_pow : (1:ℝ) ≤ 2 ^ k := one_le_pow_of_one_le (by norm_num) k
        have h_pow' : 0 ≤ (2:ℝ) ^ k - 1 := by linarith only [h_pow]
        have h_pow'' : (1:ℝ) ≤ 2 ^ (k + 1) := one_le_pow_of_one_le (by norm_num) _
        have h_pow''' : 0 ≤ (2:ℝ) ^ (k + 1) - 1 := by linarith only [h_pow'']
        have hdm_mul : 0 ≤ dm * 2 ^ k := by positivity
        have H₁ : (2 ^ k - 1) * dm ≤ (2 ^ (k + 1) - 1) * dm := by ring_nf; linarith only [hdm_mul]
        have h₁ : dist (q k um) (q (k+1) um) = 2^k * dm := by
          dsimp [q]
          rw [geodesic_segment_param_in_geodesic_spaces7]
          · rw [abs_of_nonpos]
            · ring
            · ring_nf
              linarith only [hdm_mul]
          · refine ⟨by positivity, ?_⟩
            rw [dist_comm]
            exact H₁.trans (hx₂ _ ⟨by rfl, hx₁.1⟩)
          · refine ⟨by positivity, ?_⟩
            rw [dist_comm]
            refine le_trans ?_ (hx₂ _ ⟨by rfl, hx₁.1⟩)
            ring_nf
            linarith only [hdm_mul]
        have h₂ : dist (q k w) (q (k+1) w) = 2^k * dm := by
          dsimp [q]
          rw [geodesic_segment_param_in_geodesic_spaces7]
          · rw [abs_of_nonpos]
            · ring
            · ring_nf
              linarith only [hdm_mul]
          · refine ⟨by positivity, ?_⟩
            rw [dist_comm]
            exact H₁.trans (hx₂ _ hw₁)
          · refine ⟨by positivity, ?_⟩
            rw [dist_comm]
            refine le_trans ?_ (hx₂ _ hw₁)
            ring_nf
            linarith only [hdm_mul]
        have i : q k um ∈ proj_set (q (k+1) um) (V k) := by
          refine proj_set_thickening' (hp _) ?_ H₁ ?_ (some_geodesic_is_geodesic_segment _ _).1
          · positivity
          · rw [dist_comm]
            refine le_trans ?_ (h _ ⟨by rfl, hw₁.1⟩).le
            rw [← sub_nonneg]
            ring_nf
            positivity
        have j : q k w ∈ proj_set (q (k+1) w) (V k) := by
          refine proj_set_thickening' (hp _) ?_ H₁ ?_ (some_geodesic_is_geodesic_segment _ _).1
          · positivity
          · rw [dist_comm]
            refine le_trans ?_ (h _ ⟨hw₁.1, by rfl⟩).le
            rw [← sub_nonneg]
            ring_nf
            positivity
        have : 5 * δ + 2 * QC k ≤ dist (q (k + 1) um) (q (k + 1) w) - dist (q k um) (q (k + 1) um)
                    - dist (q k w) (q (k + 1) w) + 10 * δ + 4 * QC k := by
          have := proj_along_quasiconvex_contraction (V_quasiconvex k) i j
          rw [le_max_iff] at this
          obtain h₁ | h₂ := this
          · linarith only [h₁, hw₂.1, hδ]
          · linarith only [h₂, hw₂.1, hδ]
        calc L - 4 * δ + 7 * QC (k+1) ≤ 2 * dm - 5 * δ - 2 * QC k := by
              have h₁ : QC (k + 1) = 8 * δ := by simp [QC]
              have h₂ : QC k ≤ 8 * δ := by
                dsimp only [QC]
                split_ifs
                · positivity
                · rfl
              dsimp [L]
              dsimp [D] at I₁
              linarith only [I₁, h₁, h₂, hC, hδ₀]
          _ ≤ 2^(k+1) * dm - 5 * δ - 2 * QC k := by
              gcongr
              ring_nf
              linarith only [h_pow]
          _ ≤ dist (q (k + 1) um) (q (k + 1) w) := by
              ring_nf at this h₁ h₂ ⊢
              linarith only [this, h₁, h₂]

    /- This is the end of the main induction over `k`. To conclude, choose `k` large enough
    so that the second alternative in this induction is impossible. It follows that the first
    alternative holds, i.e., the desired inequality is true. -/
    obtain ⟨k, hk⟩ : ∃ k, 2^k > dist (f um) (p um)/dm + 1 := by
      refine tendsto_pow_atTop_atTop_of_one_lt ?_ |>.eventually_gt_atTop _ |>.exists
      norm_num
    apply (Ind_k k).resolve_right
    push_neg
    intro x hx₁ hx₂
    have H₁ :=
    calc dist (f um) (p um) = ((dist (f um) (p um)/dm + 1) - 1) * dm := by field_simp
      _ < (2^k - 1) * dm := by gcongr
      _ ≤ (2^(k + 1) - 1) * dm := by
          gcongr
          · norm_num
          · linarith only []
    have H₂ := hx₂ um ⟨by rfl, hx₁.1⟩
    linarith only [H₁, H₂]
    -- end of the case where `D + 4 * C ≤ dm` and `dM ≤ dm`.

  /- This is the exact copy of the previous case, except that the roles of the points before
  and after `z` are exchanged. In a perfect world, one would use a lemma subsuming both cases,
  but in practice copy-paste seems to work better here as there are too many details to be
  changed regarding the direction of inequalities. -/
  ·
  --       then have I: "D + 4 * C ≤ dM" "dm ≤ dM" by auto
  --       define V where "V = (\<lambda>k::nat. (\<Union>g∈H. cball g ((2^k - 1) * dM)))"
  --       define QC where "QC = (\<lambda>k::nat. if k = 0 then 0 else 8 * δ)"
  --       have "QC k ≥ 0" for k unfolding QC_def using \<open>δ > 0\<close> by auto
  --       have Q: "quasiconvex (0 + 8 * deltaG X) (V k)" for k
  --         unfolding V_def apply (rule quasiconvex_thickening) using geodesic_segmentI[OF H]
  --         by (auto simp add: quasiconvex_of_geodesic)
  --       have "quasiconvex (QC k) (V k)" for k
  --         apply (cases "k = 0")
  --         apply (simp add: V_def QC_def quasiconvex_of_geodesic geodesic_segmentI[OF H])
  --         apply (rule quasiconvex_mono[OF _ Q[of k]]) using \<open>deltaG X < δ\<close> QC_def by auto
  --       define q::"nat → real → 'a" where "q = (\<lambda>k x. geodesic_segment_param {p x‒f x} (p x) ((2^k - 1) * dM))"

  --       have Ind_k: "(Gromov_product_at (f z) (f um) (f uM) ≤ Λ^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp(- K * (uM - um))))
  --             \<or> (\<exists>x ∈ {yM..uM}. (∀ y ∈ {x..uM}. dist (f y) (p y) ≥ (2^(k+1)-1) * dM) ∀  dist (q k uM) (q k x) ≥ L - 4 * δ + 7 * QC k)" for k
  --       proof (induction k)
  --         case 0
  --         have *: "\<exists>x∈ {yM..uM}. (∀ y ∈ {x..uM}. dist (f y) (p y) ≥ (2^(0+1)-1) * dM) ∀  dist (q 0 uM) (q 0 x) ≥ L - 4 * δ + 7 * QC 0"
  --         proof (rule bexI[of _ yM], auto simp add: V_def q_def QC_def)
  --           show "yM ≤ uM" using \<open>yM ∈ {z..uM}\<close> by auto
  --           show "L -4 * δ ≤ dist (p uM) (p yM)"
  --             using yM(2) apply auto using metric_space_class.zero_le_dist[of pi_z "p uM"] by linarith
  --           show "∀ y. y ≤ uM → yM ≤ y → dM ≤ dist (f y) (p y)"
  --             using dM_def closestM proj_setD(2)[OF p] by auto
  --         qed
  --         then show ?case
  --           by blast
  --       next
  --         case Suck: (Suc k)
  --         show ?case
  --         proof (cases "Gromov_product_at (f z) (f um) (f uM) ≤ Λ\<^sup>2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (uM - um)))")
  --           case True
  --           then show ?thesis by simp
  --         next
  --           case False
  --           then obtain x where x: "x ∈ {yM..uM}" "dist (q k uM) (q k x) ≥ L - 4 * δ + 7 * QC k"
  --                                  "∀ w. w ∈ {x..uM} → dist (f w) (p w) ≥ (2^(k+1)-1) * dM"
  --             using Suck.IH by auto
  --           have aux: "(2 ^ k - 1) * dM ≤ (2*2^k-1) * dM" "0 ≤ 2 * 2 ^ k - (1::real)" "dM ≤ dM * 2 ^ k"
  --             apply (auto simp add: algebra_simps)
  --             apply (metis power.simps(2) two_realpow_ge_one)
  --             using \<open>0 ≤ dM\<close> less_eq_real_def by fastforce
  --           have := calc L + C = (L/D) * (D + (D/L) * C)"
  --             using \<open>L > 0\<close> \<open>D > 0\<close> by (simp add: algebra_simps divide_simps)
  --           _ ≤ (L/D) * (D + 4 * C)"
  --             apply (intro mono_intros)
  --             using \<open>L > 0\<close> \<open>D > 0\<close> \<open>C ≥ 0\<close> \<open>D ≤ 4 * L\<close> by (auto simp add: algebra_simps divide_simps)
  --           _ ≤ (L/D) * dM"
  --             apply (intro mono_intros) using I \<open>L > 0\<close> \<open>D > 0\<close> by auto
  --           finally have "L + C ≤ (L/D) * dM"
  --             by simp
  --            moreover have "2 * δ ≤ (2 * δ)/D * dM"
  --             using I \<open>C ≥ 0\<close> \<open>δ > 0\<close> \<open>D > 0\<close> by (auto simp add: algebra_simps divide_simps)
  --           ultimately have aux2: "L + C + 2 * δ ≤ ((L + 2 * δ)/D) * dM"
  --             by (auto simp add: algebra_simps divide_simps)
  --           have aux3: "(1-α) * D + α * 2^k * dM ≤ dM * 2^k - C/2 - QC k"
  --           proof (cases "k = 0")
  --             case True
  --             show ?thesis
  --                using I \<open>C ≥ 0\<close> unfolding True QC_def alpha_def by auto
  --           next
  --             case False
  --             have := calc C/2 + QC k + (1-α) * D ≤ 2 * (1-α) * dM"
  --               using I \<open>C ≥ 0\<close> unfolding QC_def alpha_def using False Laux by auto
  --             _ ≤ 2^k * (1-α) * dM"
  --               apply (intro mono_intros) using False alphaaux I \<open>D > 0\<close> \<open>C ≥ 0\<close> by auto
  --             finally show ?thesis
  --               by (simp add: algebra_simps)
  --           qed

  --           have "\<exists>w ∈ {x..uM}. (dist (q k uM) (q k w) ∈ {(9 * δ + 4 * QC k) - 4 * δ - 2 * QC k .. 9 * δ + 4 * QC k})
  --                   ∀  (∀ v ∈ {w..uM}. dist (q k uM) (q k v) ≤ 9 * δ + 4 * QC k)"
  --           proof (rule quasi_convex_projection_small_gaps'[where ?f = f and ?G = "V k"])
  --             show "continuous_on {x..uM} f"
  --               apply (rule continuous_on_subset[OF \<open>continuous_on Icc a b f\<close>])
  --               using \<open>uM ∈ {z..b}\<close> \<open>z ∈ Icc a b\<close> \<open>yM ∈ {z..uM}\<close> \<open>x ∈ {yM..uM}\<close> by auto
  --             show "x ≤ uM" using \<open>x ∈ {yM..uM}\<close> by auto
  --             show "quasiconvex (QC k) (V k)" by fact
  --             show "deltaG TYPE('a) < δ" by fact
  --             show "9 * δ + 4 * QC k ∈ {4 * δ + 2 * QC k..dist (q k x) (q k uM)}"
  --               using x(2) \<open>δ > 0\<close> \<open>QC k ≥ 0\<close> Laux by (auto simp add: metric_space_class.dist_commute)
  --             show "q k w ∈ proj_set (f w) (V k)" if "w ∈ {x..uM}" for w
  --               unfolding V_def q_def apply (rule proj_set_thickening)
  --               using aux p x(3)[OF that] by (auto simp add: metric_space_class.dist_commute)
  --           qed
  --           then obtain w where w: "w ∈ {x..uM}"
  --                                  "dist (q k uM) (q k w) ∈ {(9 * δ + 4 * QC k) - 4 * δ - 2 * QC k .. 9 * δ + 4 * QC k}"
  --                                  "∀ v. v ∈ {w..uM} → dist (q k uM) (q k v) ≤ 9 * δ + 4 * QC k"
  --             by auto
  --           show ?thesis
  --           proof (cases "\<exists>v ∈ {w..uM}. dist (f v) (p v) ≤ (2^(k+2)-1) * dM")
  --             case True
  --             then obtain v where v: "v ∈ {w..uM}" "dist (f v) (p v) ≤ (2^(k+2)-1) * dM"
  --               by auto
  --             have aux4: "dM * 2 ^ k ≤ infDist (f r) (V k)" if "r ∈ {x..v}" for r
  --             proof -
  --               have *: "q k r ∈ proj_set (f r) (V k)"
  --                 unfolding q_def V_def apply (rule proj_set_thickening)
  --                 using aux p[of r] x(3)[of r] that \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> by (auto simp add: metric_space_class.dist_commute)
  --               have := calc infDist (f r) (V k) = dist (geodesic_segment_param {p r‒f r} (p r) (dist (p r) (f r))) (geodesic_segment_param {p r‒f r} (p r) ((2 ^ k - 1) * dM))"
  --                 using proj_setD(2)[OF *] unfolding q_def by auto
  --               _ = abs(dist (p r) (f r) - (2 ^ k - 1) * dM)"
  --                 apply (rule geodesic_segment_param(7)[where ?y = "f r"])
  --                 using x(3)[of r] \<open>r ∈ {x..v}\<close> \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> aux by (auto simp add: metric_space_class.dist_commute)
  --               _ = dist (f r) (p r) - (2 ^ k - 1) * dM"
  --                 using x(3)[of r] \<open>r ∈ {x..v}\<close> \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> aux by (auto simp add: metric_space_class.dist_commute)
  --               finally have "dist (f r) (p r) = infDist (f r) (V k) + (2 ^ k - 1) * dM" by simp
  --               moreover have "(2^(k+1) - 1) * dM ≤ dist (f r) (p r)"
  --                 apply (rule x(3)) using \<open>r ∈ {x..v}\<close> \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> by auto
  --               ultimately have "(2^(k+1) - 1) * dM ≤ infDist (f r) (V k) + (2 ^ k - 1) * dM"
  --                 by simp
  --               then show ?thesis by (auto simp add: algebra_simps)
  --             qed

  --             have "infDist (f v) H ≤ (2^(k+2)-1) * dM"
  --               using v proj_setD(2)[OF p[of v]] by auto
  --             have := calc dist closestm v ≤ Λ * (infDist (f closestm) H + (L + C + 2 * δ) + infDist (f v) H)"
  --               apply (rule D)
  --               using \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> \<open>x ∈ {yM..uM}\<close> \<open>yM ∈ {z..uM}\<close> \<open>uM ∈ {z..b}\<close> \<open>z ∈ Icc a b\<close> \<open>closestm ∈ {um..ym}\<close> \<open>ym ∈ {um..z}\<close> \<open>um ∈ {a..z}\<close> by auto
  --             _ ≤ Λ * (dm + 1 * (L + C + 2 * δ) + (2^(k+2)-1) * dM)"
  --               apply (intro mono_intros \<open>infDist (f v) H ≤ (2^(k+2)-1) * dM\<close>)
  --               using dm_def \<open>Λ ≥ 1\<close> \<open>L > 0\<close> \<open>C ≥ 0\<close> \<open>δ > 0\<close> by (auto simp add: metric_space_class.dist_commute)
  --             _ ≤ Λ * (dM + 2^k * (((L + 2 * δ)/D) * dM) + (2^(k+2)-1) * dM)"
  --               apply (intro mono_intros) using I \<open>Λ ≥ 1\<close> \<open>C ≥ 0\<close> \<open>δ > 0\<close> \<open>L > 0\<close> aux2 by auto
  --             _ = Λ * 2^k * (4 + (L + 2 * δ)/D) * dM"
  --               by (simp add: algebra_simps)
  --             finally have *: "dist closestm v / (lambda * (4 + (L + 2 * δ)/D)) ≤ 2^k * dM"
  --               using \<open>Λ ≥ 1\<close> \<open>L > 0\<close> \<open>D > 0\<close> \<open>δ > 0\<close> by (simp add: divide_simps, simp add: algebra_simps)

  --             have := calc exp(- (α * (2^k * dM) * log 2 / (5 * δ))) ≤ exp(-(α * (dist closestm v / (lambda * (4 + (L + 2 * δ)/D))) * log 2 / (5 * δ)))"
  --               apply (intro mono_intros *) using alphaaux \<open>δ > 0\<close> by auto
  --             _ = exp(-K * dist closestm v)"
  --               unfolding K_def by (simp add: divide_simps)
  --             _ = exp(-K * (v - closestm))"
  --               unfolding dist_real_def using \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> \<open>x ∈ {yM..uM}\<close> \<open>yM ∈ {z..uM}\<close> \<open>ym ∈ {um..z}\<close> \<open>closestm ∈ {um..ym}\<close> \<open>K > 0\<close> by auto
  --             finally have "exp(- (α * (2^k * dM) * log 2 / (5 * δ))) ≤ exp(-K * (v - closestm))"
  --               by simp
  --             then have := calc K * (v - x) * exp(- (α * (2^k * dM) * log 2 / (5 * δ))) ≤ K * (v - x) * exp(-K * (v - closestm))"
  --               apply (rule mult_left_mono)
  --               using \<open>δ > 0\<close> \<open>Λ ≥ 1\<close> \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> \<open>K > 0\<close> by auto
  --             _ = ((1 + K * (v - x)) - 1) * exp(- K * (v - closestm))"
  --               by (auto simp add: algebra_simps)
  --             _ ≤ (exp (K * (v - x)) - 1) * exp(-K * (v - closestm))"
  --               by (intro mono_intros, auto)
  --             _ = exp(-K * (x - closestm)) - exp(-K * (v - closestm))"
  --               by (simp add: algebra_simps mult_exp_exp)
  --             _ ≤ exp(-K * (x - closestm)) - exp(-K * (uM - um))"
  --               using \<open>K > 0\<close> \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> \<open>x ∈ {yM..uM}\<close> \<open>yM ∈ {z..uM}\<close> \<open>ym ∈ {um..z}\<close> \<open>closestm ∈ {um..ym}\<close> by auto
  --             finally have B: "(v - x) * exp(- α * 2^k * dM * log 2 / (5 * δ)) ≤
  --                                 (exp(-K * (x - closestm)) - exp(-K * (uM - um)))/K"
  --               using \<open>K > 0\<close> by (auto simp add: divide_simps algebra_simps)

  --             text \<open>The projections of $f(v)$ and $f(x)$ on the cylinder $V_k$ are well separated,
  --             by construction. This implies that $v$ and $x$ themselves are well separated.\<close>
  --             have := calc L - 4 * δ + 7 * QC k ≤ dist (q k uM) (q k x)"
  --               using x by simp
  --             _ ≤ dist (q k uM) (q k v) + dist (q k v) (q k x)"
  --               by (intro mono_intros)
  --             _ ≤ (9 * δ + 4 * QC k) + dist (q k v) (q k x)"
  --               using w(3)[of v] \<open>v ∈ {w..uM}\<close> by auto
  --             finally have := calc L - 13 * δ + 3 * QC k ≤ dist (q k x) (q k v)"
  --               by (simp add: metric_space_class.dist_commute)
  --             _ ≤ 3 * QC k + max (5 * deltaG X) ((4 * exp(1/2 * log 2)) * Λ * (v - x) * exp(-(dM * 2^k - C/2 - QC k) * log 2 / (5 * δ)))"
  --             proof (cases "k = 0")
  --               case True
  --               have "dist (q k x) (q k v) ≤ max (5 * deltaG X) ((4 * exp(1/2 * log 2)) * Λ * (v - x) * exp(-(dM * 2^k - C/2) * log 2 / (5 * δ)))"
  --               proof (rule geodesic_projection_exp_contracting[where ?G = "V k" and ?f = f])
  --                 show "geodesic_segment (V k)" unfolding V_def True using geodesic_segmentI[OF H] by auto
  --                 show "x ≤ v" using \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> by auto
  --                 show "q k v ∈ proj_set (f v) (V k)"
  --                   unfolding q_def V_def apply (rule proj_set_thickening)
  --                   using aux p[of v] x(3)[of v] \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> by (auto simp add: metric_space_class.dist_commute)
  --                 show "q k x ∈ proj_set (f x) (V k)"
  --                   unfolding q_def V_def apply (rule proj_set_thickening)
  --                   using aux p[of x] x(3)[of x] \<open>w ∈ {x..uM}\<close> by (auto simp add: metric_space_class.dist_commute)
  --                 show "15/2 * δ + C/2 ≤ dM * 2^k"
  --                   using I \<open>δ > 0\<close> \<open>C ≥ 0\<close> Laux unfolding QC_def True by auto
  --                 show "deltaG TYPE('a) < δ" by fact
  --                 show "∀ t. t ∈ {x..v} → dM * 2 ^ k ≤ infDist (f t) (V k)"
  --                   using aux4 by auto
  --                 show "0 ≤ C" "0 ≤ Λ" using \<open>C ≥ 0\<close> \<open>Λ ≥ 1\<close> by auto
  --                 show "dist (f x1) (f x2) ≤ Λ * dist x1 x2 + C" if "x1 ∈ {x..v}" "x2 ∈ {x..v}" for x1 x2
  --                   using quasi_isometry_onD(1)[OF assms(2)] that \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> \<open>x ∈ {yM..uM}\<close> \<open>yM ∈ {z..uM}\<close> \<open>uM ∈ {z..b}\<close> \<open>z ∈ Icc a b\<close> by auto
  --               qed
  --               then show ?thesis unfolding QC_def True by auto
  --             next
  --               case False
  --               have "dist (q k x) (q k v) ≤ 2 * QC k + 8 * δ + max (5 * deltaG X) ((4 * exp(1/2 * log 2)) * Λ * (v - x) * exp(-(dM * 2^k - QC k - C/2) * log 2 / (5 * δ)))"
  --               proof (rule quasiconvex_projection_exp_contracting[where ?G = "V k" and ?f = f])
  --                 show "quasiconvex (QC k) (V k)" by fact
  --                 show "x ≤ v" using \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> by auto
  --                 show "q k v ∈ proj_set (f v) (V k)"
  --                   unfolding q_def V_def apply (rule proj_set_thickening)
  --                   using aux p[of v] x(3)[of v] \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> by (auto simp add: metric_space_class.dist_commute)
  --                 show "q k x ∈ proj_set (f x) (V k)"
  --                   unfolding q_def V_def apply (rule proj_set_thickening)
  --                   using aux p[of x] x(3)[of x] \<open>w ∈ {x..uM}\<close> by (auto simp add: metric_space_class.dist_commute)
  --                 show "15/2 * δ + QC k + C/2 ≤ dM * 2^k"
  --                   apply (rule order_trans[of _ dM])
  --                   using I \<open>δ > 0\<close> \<open>C ≥ 0\<close> Laux unfolding QC_def by auto
  --                 show "deltaG TYPE('a) < δ" by fact
  --                 show "∀ t. t ∈ {x..v} → dM * 2 ^ k ≤ infDist (f t) (V k)"
  --                   using aux4 by auto
  --                 show "0 ≤ C" "0 ≤ Λ" using \<open>C ≥ 0\<close> \<open>Λ ≥ 1\<close> by auto
  --                 show "dist (f x1) (f x2) ≤ Λ * dist x1 x2 + C" if "x1 ∈ {x..v}" "x2 ∈ {x..v}" for x1 x2
  --                   using quasi_isometry_onD(1)[OF assms(2)] that \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> \<open>x ∈ {yM..uM}\<close> \<open>yM ∈ {z..uM}\<close> \<open>uM ∈ {z..b}\<close> \<open>z ∈ Icc a b\<close> by auto
  --               qed
  --               then show ?thesis unfolding QC_def using False by (auto simp add: algebra_simps)
  --             qed
  --             finally have "L - 13 * δ ≤ max (5 * deltaG X) ((4 * exp(1/2 * log 2)) * Λ * (v - x) * exp(-(dM * 2^k - C/2 - QC k) * log 2 / (5 * δ)))"
  --               by auto
  --             then have := calc L - 13 * δ ≤ (4 * exp(1/2 * log 2)) * Λ * (v - x) * exp(-(dM * 2^k - C/2 - QC k) * log 2 / (5 * δ))"
  --               using \<open>δ > deltaG X\<close> Laux by auto
  --             _ ≤ (4 * exp(1/2 * log 2)) * Λ * (v - x) * exp(-((1-α) * D + α * 2^k * dM) * log 2 / (5 * δ))"
  --               apply (intro mono_intros) using aux3 \<open>δ > 0\<close> \<open>Λ ≥ 1\<close> \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> by auto
  --             _ = (4 * exp(1/2 * log 2)) * Λ * (v - x) * (exp(-(1-α) * D * log 2 / (5 * δ)) * exp(-α * 2^k * dM * log 2 / (5 * δ)))"
  --               unfolding mult_exp_exp by (auto simp add: algebra_simps divide_simps)
  --             finally have A: "L - 13 * δ ≤ (4 * exp(1/2 * log 2)) * Λ * exp(-(1-α) * D * log 2 / (5 * δ)) * ((v - x) * exp(-α * 2^k * dM * log 2 / (5 * δ)))"
  --               by (simp add: algebra_simps)

  --             _ ≤ (4 * exp(1/2 * log 2)) * Λ * exp 0 * ((v - x) * exp 0)"
  --               apply (intro mono_intros) using \<open>δ > 0\<close> \<open>Λ ≥ 1\<close> \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> alphaaux \<open>D > 0\<close> \<open>C ≥ 0\<close> I
  --               by (auto simp add: divide_simps mult_nonpos_nonneg)
  --             _ = (4 * exp(1/2 * log 2)) * Λ * (v - x)"
  --               by simp
  --             _ ≤ 20 * Λ * (v - x)"
  --               apply (intro mono_intros, approximation 10)
  --               using \<open>δ > 0\<close> \<open>Λ ≥ 1\<close> \<open>v ∈ {w..uM}\<close> \<open>w ∈ {x..uM}\<close> by auto
  --             finally have "v - x ≥ (1/4) * δ / Λ"
  --               using \<open>Λ ≥ 1\<close> L_def \<open>δ > 0\<close> by (simp add: divide_simps algebra_simps)
  --             then have := calc x - closestm + (1/4) * δ / Λ ≤ v - closestm"
  --               by simp
  --             _ ≤ uM - um"
  --               using \<open>closestm ∈ {um..ym}\<close> \<open>v ∈ {w..uM}\<close> by auto
  --             _ ≤ Suc n * (1/4) * δ / Λ" by fact
  --             finally have "x - closestm ≤ n * (1/4) * δ / Λ"
  --               unfolding Suc_eq_plus1 by (auto simp add: algebra_simps add_divide_distrib)

  --             have := calc L + 4 * δ = ((L + 4 * δ)/(L - 13 * δ)) * (L - 13 * δ)"
  --               using Laux \<open>δ > 0\<close> by (simp add: algebra_simps divide_simps)
  --             _ ≤ ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp(1/2 * log 2)) * Λ * exp (- (1 - α) * D * log 2 / (5 * δ)) * ((v - x) * exp (- α * 2 ^ k * dM * log 2 / (5 * δ))))"
  --               apply (rule mult_left_mono) using A Laux \<open>δ > 0\<close> by (auto simp add: divide_simps)
  --             _ ≤ ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp(1/2 * log 2)) * Λ * exp (- (1 - α) * D * log 2 / (5 * δ)) * ((exp(-K * (x - closestm)) - exp(-K * (uM - um)))/K))"
  --               apply (intro mono_intros B) using Laux \<open>δ > 0\<close> \<open>Λ ≥ 1\<close> by (auto simp add: divide_simps)
  --             finally have C: "L + 4 * δ ≤ Kmult * (exp(-K * (x - closestm)) - exp(-K * (uM - um)))"
  --               unfolding Kmult_def by argo

  --             have := calc Gromov_product_at (f z) (f um) (f uM) ≤ Gromov_product_at (f z) (f closestm) (f x) + (L + 4 * δ)"
  --               apply (rule Rec) using \<open>closestm ∈ {um..ym}\<close> \<open>x ∈ {yM..uM}\<close> \<open>yM ∈ {z..uM}\<close> by auto
  --             _ ≤ (lambda^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp(- K * (x - closestm)))) + (Kmult * (exp(-K * (x - closestm)) - exp(-K * (uM-um))))"
  --               apply (intro mono_intros C Suc.IH)
  --               using \<open>x ∈ {yM..uM}\<close> \<open>yM ∈ {z..uM}\<close> \<open>um ∈ {a..z}\<close> \<open>closestm ∈ {um..ym}\<close> \<open>ym ∈ {um..z}\<close> \<open>uM ∈ {z..b}\<close> \<open>x - closestm ≤ n * (1/4) * δ / Λ\<close> by auto
  --             _ = (lambda^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp(- K * (uM - um))))"
  --               unfolding K_def by (simp add: algebra_simps)
  --             finally show ?thesis by auto
  --           next
  --             case False
  --             have "\<exists>w∈{yM..uM}. (∀ r∈{w..uM}. (2 ^ (Suc k + 1) - 1) * dM ≤ dist (f r) (p r)) ∀  L - 4 * δ + 7 * QC (Suc k) ≤ dist (q (Suc k) uM) (q (Suc k) w)"
  --             proof (rule bexI[of _ w], auto)
  --               show "w ≤ uM" "yM ≤ w" using \<open>w ∈ {x..uM}\<close> \<open>x ∈ {yM..uM}\<close> by auto
  --               show "(4 * 2 ^ k - 1) * dM ≤ dist (f x) (p x)" if "x ≤ uM" "w ≤ x" for x
  --                 using False \<open>dM ≥ 0\<close> that by force

  --               have "dist (q k uM) (q (k+1) uM) = 2^k * dM"
  --                 unfolding q_def apply (subst geodesic_segment_param(7)[where ?y = "f uM"])
  --                 using x(3)[of uM] \<open>x ∈ {yM..uM}\<close> aux by (auto simp add: metric_space_class.dist_commute, simp add: algebra_simps)
  --               have "dist (q k w) (q (k+1) w) = 2^k * dM"
  --                 unfolding q_def apply (subst geodesic_segment_param(7)[where ?y = "f w"])
  --                 using x(3)[of w] \<open>w ∈ {x..uM}\<close> \<open>x ∈ {yM..uM}\<close> aux by (auto simp add: metric_space_class.dist_commute, simp add: algebra_simps)
  --               have i: "q k uM ∈ proj_set (q (k+1) uM) (V k)"
  --                 unfolding q_def V_def apply (rule proj_set_thickening'[of _ "f uM"])
  --                 using p x(3)[of uM] \<open>x ∈ {yM..uM}\<close> aux by (auto simp add: algebra_simps metric_space_class.dist_commute)
  --               have j: "q k w ∈ proj_set (q (k+1) w) (V k)"
  --                 unfolding q_def V_def apply (rule proj_set_thickening'[of _ "f w"])
  --                 using p x(3)[of w] \<open>x ∈ {yM..uM}\<close> \<open>w ∈ {x..uM}\<close> aux by (auto simp add: algebra_simps metric_space_class.dist_commute)

  --               have := calc 5 * δ + 2 * QC k ≤ dist (q k uM) (q k w)" using w(2) by simp
  --               _ ≤ max (5 * deltaG X + 2 * QC k)
  --                                     (dist (q (k + 1) uM) (q (k + 1) w) - dist (q k uM) (q (k + 1) uM) - dist (q k w) (q (k + 1) w) + 10 * deltaG X + 4 * QC k)"
  --                 by (rule proj_along_quasiconvex_contraction[OF \<open>quasiconvex (QC k) (V k)\<close> i j])
  --               finally have "5 * δ + 2 * QC k ≤ dist (q (k + 1) uM) (q (k + 1) w) - dist (q k uM) (q (k + 1) uM) - dist (q k w) (q (k + 1) w) + 10 * deltaG X + 4 * QC k"
  --                 using \<open>deltaG X < δ\<close> by auto
  --               then have := calc 0 ≤ dist (q (k + 1) uM) (q (k + 1) w) + 5 * δ + 2 * QC k - dist (q k uM) (q (k + 1) uM) - dist (q k w) (q (k + 1) w)"
  --                 using \<open>deltaG X < δ\<close> by auto
  --               _ = dist (q (k + 1) uM) (q (k + 1) w) + 5 * δ + 2 * QC k - 2^(k+1) * dM"
  --                 by (simp only: \<open>dist (q k w) (q (k+1) w) = 2^k * dM\<close> \<open>dist (q k uM) (q (k+1) uM) = 2^k * dM\<close>, auto)
  --               finally have *: "2^(k+1) * dM - 5 * δ - 2 * QC k ≤ dist (q (k+1) uM) (q (k+1) w)"
  --                 using \<open>deltaG X < δ\<close> by auto
  --               have := calc L - 4 * δ + 7 * QC (k+1) ≤ 2 * dM - 5 * δ - 2 * QC k"
  --                 unfolding QC_def L_def using \<open>δ > 0\<close> Laux I \<open>C ≥ 0\<close> by auto
  --               _ ≤ 2^(k+1) * dM - 5 * δ - 2 * QC k"
  --                 using aux by (auto simp add: algebra_simps)
  --               finally show "L - 4 * δ + 7 * QC (Suc k) ≤ dist (q (Suc k) uM) (q (Suc k) w)"
  --                 using * by auto
  --             qed
  --             then show ?thesis
  --               by simp
  --           qed
  --         qed
  --       qed
  --       have "dM > 0" using I \<open>δ > 0\<close> \<open>C ≥ 0\<close> Laux by auto
  --       have "\<exists>k. 2^k > dist (f uM) (p uM)/dM + 1"
  --         by (simp add: real_arch_pow)
  --       then obtain k where "2^k > dist (f uM) (p uM)/dM + 1"
  --         by blast
  --       then have := calc dist (f uM) (p uM) < (2^k - 1) * dM"
  --         using \<open>dM > 0\<close> by (auto simp add: divide_simps algebra_simps)
  --       _ ≤ (2^(Suc k) - 1) * dM"
  --         by (intro mono_intros, auto)
  --       finally have "\<not>((2 ^ (k + 1) - 1) * dM ≤ dist (f uM) (p uM))"
  --         by simp
  --       then show "Gromov_product_at (f z) (f um) (f uM) ≤ Λ\<^sup>2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (uM - um)))"
  --         using Ind_k[of k] by auto
  --     qed
  --   qed
  -- qed
    sorry


/-- The main induction is over. To conclude, one should apply its result to the original
geodesic segment joining the points $f(a)$ and $f(b)$. -/
lemma Morse_Gromov_theorem_aux1
    {f : ℝ → X} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    {Λ C : ℝ} (hf' : quasi_isometry_on Λ C (Icc a b) f)
    (hab : a ≤ b)
    {G : Set X} (hGf : geodesic_segment_between G (f a) (f b))
    {z : ℝ} (hz : z ∈ Icc a b)
    {δ : ℝ} (hδ : δ > deltaG X) :
    infDist (f z) G ≤ Λ ^ 2 * (11/2 * C + 95 * δ) := by
  have := hf'.C_nonneg
  have := hf'.one_le_lambda
  have : Inhabited X := ⟨f 0⟩
  have : 0 < δ := by linarith only [hδ, delta_nonneg X]

  /- We give their values to the parameters `L`, `D` and `α` that we will use in the proof.
  We also define two constants $K$ and $K_{mult}$ that appear in the precise formulation of the
  bounds. Their values have no precise meaning, they are just the outcome of the computation. -/
  let α : ℝ := 12/100
  let L : ℝ := 18 * δ
  let D : ℝ := 55 * δ
  let K : ℝ := α * log 2 / (5 * (4 + (L + 2 * δ)/D) * δ * Λ)
  let Kmult : ℝ := ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp (1/2 * log 2)) * Λ * exp (- ((1 - α) * D * log 2 / (5 * δ))) / K)

  obtain ⟨n, hn⟩ : ∃ n : ℕ, (b - a)/((1/4) * δ / Λ) ≤ n := exists_nat_ge _
  have : b - a ≤ n * (1/4) * δ / Λ := by
    rw [div_le_iff] at hn
    · convert hn using 1
      ring
    · positivity
  calc infDist (f z) G
      ≤ Gromov_product_at (f z) (f a) (f b) + 2 * deltaG X := infDist_triangle_side _ hGf
    _ ≤ (Λ^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (-K * (b - a)))) + 2 * δ := by
        gcongr
        refine Morse_Gromov_theorem_aux0 hf hf' hab hGf hz hδ n a b ?_ ?_ this
        · exact ⟨by rfl, hz.1⟩
        · exact ⟨hz.2, by rfl⟩
    _ = Λ^2 * (D + 3/2 * L + δ + 11/2 * C) + Kmult * (1 - exp (-K * (b - a))) := by ring
    _ ≤ Λ^2 * (D + 3/2 * L + δ + 11/2 * C) + Kmult * (1 - 0) := by
        gcongr
        · dsimp [Kmult, L, D]
          ring_nf
          positivity
        · positivity
    _ = Λ^2 * (11/2 * C + (3200 * exp (-(459/50*log 2))/log 2 + 83) * δ) := by
        dsimp [Kmult, K, L, D, α]
        ring_nf
        field_simp
        rw [mul_assoc Λ, ← exp_add]
        ring_nf
    _ ≤ Λ^2 * (11/2 * C + 95 * δ) := by
        gcongr
        have := log_two_gt_d9
        have := exp_one_gt_d9
        calc 3200 * exp (-(459 / 50 * log 2)) / log 2 + 83
            ≤ 3200 * exp (-(459 / 50 * 0.6931471803)) / 0.6931471803 + 83 := by gcongr
          _ ≤ 3200 * exp (-6) / 0.6931471803 + 83 := by
              gcongr
              norm_num
          _ = 3200 * (1 / exp 1 ^ (6 : ℕ)) / 0.6931471803 + 83 := by
              rw [exp_neg]
              field_simp
          _ ≤ 3200 * (1 / 2.7182818283 ^ (6 : ℕ)) / 0.6931471803 + 83 := by gcongr
          _ ≤ 95 := by norm_num1

/-- Still assuming that our quasi-isometry is Lipschitz, we will improve slightly on the previous
result, first going down to the hyperbolicity constant of the space, and also showing that,
conversely, the geodesic is contained in a neighborhood of the quasi-geodesic. The argument for this
last point goes as follows. Consider a point `x` on the geodesic. Define two sets to
be the `D`-thickenings of $[a,x]$ and $[x,b]$ respectively, where `D` is such that any point on the
quasi-geodesic is within distance `D` of the geodesic (as given by the previous theorem). The union
of these two sets covers the quasi-geodesic, and they are both closed and nonempty. By connectedness,
there is a point `z` in their intersection, `D`-close both to a point `x⁻` before `x` and to a point
`x⁺` after `x`. Then `x` belongs to a geodesic between `x⁻` and `x⁺`, which is contained in a
`4 * δ`-neighborhood of geodesics from `x⁻` to `z` and from `x⁺` to `z` by hyperbolicity. It
follows that `x` is at distance at most `D + 4 * δ` of `z`, concluding the proof. -/
lemma Morse_Gromov_theorem_aux2
    {f : ℝ → X} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    {Λ C : ℝ} (hf' : quasi_isometry_on Λ C (Icc a b) f)
    {G : Set X} (hG : geodesic_segment_between G (f a) (f b)) :
    hausdorffDist (f '' (Icc a b)) G ≤ Λ^2 * (11/2 * C + 92 * deltaG X) := by
  sorry

#exit
proof (cases "a ≤ b")
  case True
  have "lambda ≥ 1" "C ≥ 0" using quasi_isometry_onD[OF assms(2)] by auto
  have *: "infDist (f z) G ≤ Λ^2 * (11/2 * C + 91 * δ)" if "z ∈ Icc a b" "δ > deltaG X" for z delta
    by (rule Morse_Gromov_theorem_aux1[OF assms(1) assms(2) True assms(3) that])
  define D where "D = Λ^2 * (11/2 * C + 91 * deltaG X)"
  have "D ≥ 0" unfolding D_def using \<open>C ≥ 0\<close> by auto
  have I: "infDist (f z) G ≤ D" if "z ∈ Icc a b" for z
  proof -
    have "(infDist (f z) G/ Λ^2 - 11/2 * C)/91 ≤ δ" if "δ > deltaG X" for delta
      using *[OF \<open>z ∈ Icc a b\<close> that] \<open>Λ ≥ 1\<close> by (auto simp add: divide_simps algebra_simps)
    then have "(infDist (f z) G/ Λ^2 - 11/2 * C)/91 ≤ deltaG X"
      using dense_ge by blast
    then show ?thesis unfolding D_def using \<open>Λ ≥ 1\<close> by (auto simp add: divide_simps algebra_simps)
  qed
  show ?thesis
  proof (rule hausdorff_distanceI)
    show "0 ≤ Λ\<^sup>2 * (11/2 * C + 92 * deltaG TYPE('a))" using \<open>C ≥ 0\<close> by auto
    fix x assume "x ∈ f`Icc a b"
    then obtain z where z: "x = f z" "z ∈ Icc a b" by blast
    show "infDist x G ≤ Λ\<^sup>2 * (11/2 * C + 92 * deltaG TYPE('a))"
      unfolding z(1) by (rule order_trans[OF I[OF \<open>z ∈ Icc a b\<close>]], auto simp add: algebra_simps D_def)
  next
    fix x assume "x ∈ G"
    have "infDist x (f`Icc a b) ≤ D + 1 * deltaG TYPE('a)"
    proof -
      define p where "p = geodesic_segment_param G (f a)"
      then have p: "p 0 = f a" "p (dist (f a) (f b)) = f b"
        unfolding p_def using assms(3) by auto
      obtain t where t: "x = p t" "t ∈ {0..dist (f a) (f b)}"
        unfolding p_def using \<open>x ∈ G\<close> \<open>geodesic_segment_between G (f a) (f b)\<close> by (metis geodesic_segment_param(5) imageE)
      define Km where "Km = (\<Union>z ∈ p`{0..t}. cball z D)"
      define KM where "KM = (\<Union>z ∈ p`{t..dist (f a) (f b)}. cball z D)"
      have "f`Icc a b \<subseteq> Km \<union> KM"
      proof
        fix x assume x: "x ∈ f`Icc a b"
        have "\<exists>z ∈ G. infDist x G = dist x z"
          apply (rule infDist_proper_attained)
          using geodesic_segment_topology[OF geodesic_segmentI[OF assms(3)]] by auto
        then obtain z where z: "z ∈ G" "infDist x G = dist x z"
          by auto
        obtain tz where tz: "z = p tz" "tz ∈ {0..dist (f a) (f b)}"
          unfolding p_def using \<open>z ∈ G\<close> \<open>geodesic_segment_between G (f a) (f b)\<close> by (metis geodesic_segment_param(5) imageE)
        have "infDist x G ≤ D"
          using I \<open>x ∈ f`Icc a b\<close> by auto
        then have "dist z x ≤ D"
          using z(2) by (simp add: metric_space_class.dist_commute)
        then show "x ∈ Km \<union> KM"
          unfolding Km_def KM_def using tz by force
      qed
      then have *: "f`Icc a b = (Km \<inter> f`Icc a b) \<union> (KM \<inter> f`Icc a b)" by auto
      have "(Km \<inter> f`Icc a b) \<inter> (KM \<inter> f`Icc a b) \<noteq> {}"
      proof (rule connected_as_closed_union[OF _ *])
        have "closed (f ` Icc a b)"
          apply (intro compact_imp_closed compact_continuous_image) using assms(1) by auto
        have "closed Km"
          unfolding Km_def apply (intro compact_has_closed_thickening compact_continuous_image)
          apply (rule continuous_on_subset[of "{0..dist (f a) (f b)}" p])
          unfolding p_def using assms(3) \<open>t ∈ {0..dist (f a) (f b)}\<close> by (auto simp add: isometry_on_continuous)
        then show "closed (Km \<inter> f`Icc a b)"
          by (rule topological_space_class.closed_Int) fact

        have "closed KM"
          unfolding KM_def apply (intro compact_has_closed_thickening compact_continuous_image)
          apply (rule continuous_on_subset[of "{0..dist (f a) (f b)}" p])
          unfolding p_def using assms(3) \<open>t ∈ {0..dist (f a) (f b)}\<close> by (auto simp add: isometry_on_continuous)
        then show "closed (KM \<inter> f`Icc a b)"
          by (rule topological_space_class.closed_Int) fact

        show "connected (f`Icc a b)"
          apply (rule connected_continuous_image) using assms(1) by auto
        have "f a ∈ Km \<inter> f`Icc a b" using True apply auto
          unfolding Km_def apply auto apply (rule bexI[of _ 0])
          unfolding p using \<open>D ≥ 0\<close> t(2) by auto
        then show "Km \<inter> f`Icc a b \<noteq> {}" by auto
        have "f b ∈ KM \<inter> f`Icc a b" apply auto
          unfolding KM_def apply auto apply (rule bexI[of _ "dist (f a) (f b)"])
          unfolding p using \<open>D ≥ 0\<close> t(2) True by auto
        then show "KM \<inter> f`Icc a b \<noteq> {}" by auto
      qed
      then obtain y where y: "y ∈ f`Icc a b" "y ∈ Km" "y ∈ KM" by auto
      obtain tm where tm: "tm ∈ {0..t}" "dist (p tm) y ≤ D"
        using y(2) unfolding Km_def by auto
      obtain tM where tM: "tM ∈ {t..dist (f a) (f b)}" "dist (p tM) y ≤ D"
        using y(3) unfolding KM_def by auto
      define H where "H = p`{tm..tM}"
      have *: "geodesic_segment_between H (p tm) (p tM)"
        unfolding H_def p_def apply (rule geodesic_segmentI2)
        using assms(3) \<open>tm ∈ {0..t}\<close> \<open>tM ∈ {t..dist (f a) (f b)}\<close> isometry_on_subset
        using assms(3) geodesic_segment_param(4) by (auto) fastforce
      have "x ∈ H"
        unfolding t(1) H_def using \<open>tm ∈ {0..t}\<close> \<open>tM ∈ {t..dist (f a) (f b)}\<close> by auto
      have := calc infDist x (f ` Icc a b) ≤ dist x y"
        by (rule infDist_le[OF y(1)])
      _ ≤ max (dist (p tm) y) (dist (p tM) y) + deltaG X"
        by (rule dist_le_max_dist_triangle[OF * \<open>x ∈ H\<close>])
      finally show ?thesis
        using tm(2) tM(2) by auto
    qed
    _ ≤ D + Λ^2 * deltaG TYPE('a)"
      apply (intro mono_intros) using \<open>Λ ≥ 1\<close> by auto
    finally show "infDist x (f ` Icc a b) ≤ Λ\<^sup>2 * (11/2 * C + 92 * deltaG TYPE('a))"
      unfolding D_def by (simp add: algebra_simps)
  qed
next
  case False
  then have "f`Icc a b = {}"
    by auto
  then have "hausdorff_distance (f ` Icc a b) G = 0"
    unfolding hausdorff_distance_def by auto
  then show ?thesis
    using quasi_isometry_onD(4)[OF assms(2)] by auto
qed

text \<open>The full statement of the Morse-Gromov Theorem, asserting that a quasi-geodesic is
within controlled distance of a geodesic with the same endpoints. It is given in the formulation
of Shchur~\<^cite>\<open>"shchur"\<close>, with optimal control in terms of the parameters of the quasi-isometry.
This statement follows readily from the previous one and from the fact that quasi-geodesics can be
approximated by Lipschitz ones.\<close>

theorem (in Gromov_hyperbolic_space_geodesic) Morse_Gromov_theorem:
  fixes f::"real → 'a"
  assumes "lambda C-quasi_isometry_on Icc a b f"
          "geodesic_segment_between G (f a) (f b)"
  shows "hausdorff_distance (f`Icc a b) G ≤ 92 * Λ^2 * (C + deltaG X)"
proof -
  have C: "C ≥ 0" "lambda ≥ 1" using quasi_isometry_onD[OF assms(1)] by auto
  consider "dist (f a) (f b) ≥ 2 * C ∀  a ≤ b" | "dist (f a) (f b) ≤ 2 * C ∀  a ≤ b" | "b < a"
    by linarith
  then show ?thesis
  proof (cases)
    case 1
    have "\<exists>d. continuous_on Icc a b d ∀  d a = f a ∀  d b = f b
                ∀  (∀ x∈Icc a b. dist (f x) (d x) ≤ 4 * C)
                ∀  Λ (4 * C)-quasi_isometry_on Icc a b d
                ∀  (2 * Λ)-lipschitz_on Icc a b d
                ∀  hausdorff_distance (f`Icc a b) (d`Icc a b) ≤ 2 * C"
      apply (rule quasi_geodesic_made_lipschitz[OF assms(1)]) using 1 by auto
    then obtain d where d: "d a = f a" "d b = f b"
                        "∀ x. x ∈ Icc a b → dist (f x) (d x) ≤ 4 * C"
                        "lambda (4 * C)-quasi_isometry_on Icc a b d"
                        "(2 * Λ)-lipschitz_on Icc a b d"
                        "hausdorff_distance (f`Icc a b) (d`Icc a b) ≤ 2 * C"
      by auto
    have a: "hausdorff_distance (d`Icc a b) G ≤ Λ^2 * ((11/2) * (4 * C) + 92 * deltaG X)"
      apply (rule Morse_Gromov_theorem_aux2) using d assms lipschitz_on_continuous_on by auto

    have := calc hausdorff_distance (f`Icc a b) G ≤
          hausdorff_distance (f`Icc a b) (d`Icc a b) + hausdorff_distance (d`Icc a b) G"
      apply (rule hausdorff_distance_triangle)
      using 1 apply simp
      by (rule quasi_isometry_on_bounded[OF d(4)], auto)
    _ ≤ Λ^2 * ((11/2) * (4 * C) + 92 * deltaG X) + 1 * 2 * C"
      using a d by auto
    _ ≤ Λ^2 * ((11/2) * (4 * C) + 92 * deltaG X) + Λ^2 * 2 * C"
      apply (intro mono_intros) using \<open>Λ ≥ 1\<close> \<open>C ≥ 0\<close> by auto
    _ = Λ^2 * (24 * C + 92 * deltaG X)"
      by (simp add: algebra_simps divide_simps)
    _ ≤ Λ^2 * (92 * C + 92 * deltaG X)"
      apply (intro mono_intros) using \<open>Λ ≥ 1\<close> \<open>C ≥ 0\<close> by auto
    finally show ?thesis by (auto simp add: algebra_simps)
  next
    case 2
    have := calc (1/lambda) * dist a b - C ≤ dist (f a) (f b)"
      apply (rule quasi_isometry_onD[OF assms(1)]) using 2 by auto
    _ ≤ 2 * C" using 2 by auto
    finally have "dist a b ≤ 3 * Λ * C"
      using C by (auto simp add: algebra_simps divide_simps)
    then have *: "b - a ≤ 3 * Λ * C" using 2 unfolding dist_real_def by auto
    show ?thesis
    proof (rule hausdorff_distanceI2)
      show "0 ≤ 92 * Λ\<^sup>2 * (C + deltaG TYPE('a))" using C by auto
      fix x assume "x ∈ f`Icc a b"
      then obtain t where t: "x = f t" "t ∈ Icc a b" by auto
      have := calc dist x (f a) ≤ Λ * dist t a + C"
        unfolding t(1) using quasi_isometry_onD(1)[OF assms(1) t(2)] 2 by auto
      _ ≤ Λ * (b - a) + 1 * 1 * C + 0 * 0 * deltaG X" using t(2) 2 C unfolding dist_real_def by auto
      _ ≤ Λ * (3 * Λ * C) + Λ^2 * (92-3) * C + Λ^2 * 92 * deltaG X"
        apply (intro mono_intros *) using C by auto
      finally have *: "dist x (f a) ≤ 92 * Λ\<^sup>2 * (C + deltaG TYPE('a))"
        by (simp add: algebra_simps power2_eq_square)
      show "\<exists>y∈G. dist x y ≤ 92 * Λ\<^sup>2 * (C + deltaG TYPE('a))"
        apply (rule bexI[of _ "f a"]) using * 2 assms(2) by auto
    next
      fix x assume "x ∈ G"
      then have := calc dist x (f a) ≤ dist (f a) (f b)"
        by (meson assms geodesic_segment_dist_le geodesic_segment_endpoints(1) local.some_geodesic_is_geodesic_segment(1))
      _ ≤ 1 * 2 * C + Λ^2 * 0 * deltaG X"
        using 2 by auto
      _ ≤ Λ^2 * 92 * C + Λ^2 * 92 * deltaG X"
        apply (intro mono_intros) using C by auto
      finally have *: "dist x (f a) ≤ 92 * Λ\<^sup>2 * (C + deltaG TYPE('a))"
        by (simp add: algebra_simps)
      show "\<exists>y∈f`Icc a b. dist x y ≤ 92 * Λ\<^sup>2 * (C + deltaG TYPE('a))"
        apply (rule bexI[of _ "f a"]) using * 2 by auto
    qed
  next
    case 3
    then have "hausdorff_distance (f ` Icc a b) G = 0"
      unfolding hausdorff_distance_def by auto
    then show ?thesis
      using C by auto
  qed
qed

text \<open>This theorem implies the same statement for two quasi-geodesics sharing their endpoints.\<close>

theorem (in Gromov_hyperbolic_space_geodesic) Morse_Gromov_theorem2:
  fixes c d::"real → 'a"
  assumes "lambda C-quasi_isometry_on Icc a b c"
          "lambda C-quasi_isometry_on Icc a b d"
          "c A = d A" "c B = d B"
  shows "hausdorff_distance (c`Icc a b) (d`Icc a b) ≤ 184 * Λ^2 * (C + deltaG X)"
proof (cases "A ≤ B")
  case False
  then have "hausdorff_distance (c`Icc a b) (d`Icc a b) = 0" by auto
  then show ?thesis using quasi_isometry_onD[OF assms(1)] delta_nonneg by auto
next
  case True
  have "hausdorff_distance (c`Icc a b) {c A‒c B} ≤ 92 * Λ^2 * (C + deltaG X)"
    by (rule Morse_Gromov_theorem[OF assms(1)], auto)
  moreover have "hausdorff_distance {c A‒c B} (d`Icc a b) ≤ 92 * Λ^2 * (C + deltaG X)"
    unfolding \<open>c A = d A\<close> \<open>c B = d B\<close> apply (subst hausdorff_distance_sym)
    by (rule Morse_Gromov_theorem[OF assms(2)], auto)
  moreover have "hausdorff_distance (c`Icc a b) (d`Icc a b) ≤ hausdorff_distance (c`Icc a b) {c A‒c B} + hausdorff_distance {c A‒c B} (d`Icc a b)"
    apply (rule hausdorff_distance_triangle)
    using True compact_imp_bounded[OF some_geodesic_compact] by auto
  ultimately show ?thesis by auto
qed
