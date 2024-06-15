/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD -/
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Util.Time
import GromovHyperbolicity.Prereqs.QuasiIsometry
import GromovHyperbolicity.QuasiconvexProjectionExpContracting

open Set Metric Real Classical Filter

/-! # Gromov product bound for quasigeodesics

The statement in this file is the main step in the proof of the Morse-Gromov theorem given by Shchur
in~\<^cite>\<open>"shchur"\<close>, asserting that a quasi-geodesic and a geodesic with the same endpoints are close.
We show that a point on the quasi-geodesic is close in Gromov product to its endpoints.
We also assume that the quasi-geodesic is parameterized by a Lipschitz map
-- the general case will follow as any quasi-geodesic can be approximated by a Lipschitz map with
good controls.

Here is a sketch of the proof. Fix two large constants `L ≤ D` (that we will choose carefully
to optimize the values of the constants at the end of the proof). Consider a quasi-geodesic `f`
between two points `f um` and `f u`$.
Fix `f z`. We want to find a bound on `gromovProductAt (f z) (f um) (f uM)`.
1 - If this distance is smaller than `L`, we are done (and the bound is `L`).
2 - Assume it is larger.
Let `m` be the point on $[f um, f uM]$ opposite to `f z` in the tripod,
i.e., at distance `gromovProductAt (f um) (f z) (f uM)` of `f um`, and at distance
`gromovProductAt (f uM) (f z) (f um)` of `f uM`.
Let `H` be a geodesic from `f z` to `m`, and let `pi_z` denote the point on `H` at distance
`gromovProductAt (f z) (f um) (f uM)` of `f z`. (It is within distance `2 * δ` of `m`).
Let `pi_z` be approximately the projection of `f z` on the geodesic between the two endpoints,
and let `H` be a geodesic between `z` and `pi_z`.

The idea will be to project the image of `f` on `H`, and record how much
progress is made towards `f z`. In this proof, we will construct several points before and after
`z`. When necessary, we put an exponent $-$ on the points before `z`, and `+` on the points after
`z`. To ease the reading, the points are ordered following the alphabetical order, i.e.,
`um ≤ v ≤ w ≤ x ≤ y^- ≤ z`.

One can find two points $f ym$ and $f yM$ on the left and the right of `f z` that project
on `H` roughly at distance `L` of `pi_z` (up to some $O(δ)$ -- recall that the closest point
projection is not uniquely defined, and not continuous, so we make some choice here).
Let $dM$ be the minimal distance of $f([um, ym])$ to $H$, and let $dM$ be the minimal distance
of $f([yM, uM)]$ to $H$.

2.1 If the two distances $dm$ and $dM$ are less than `D`, then the distance between two points
realizing the minimum (say $f(c^-)$ and $f(c^+)$) is at most `2 * D + L`, hence $c^+ - c^-$ is controlled
(by `Λ * (2 * D + L) + C`) thanks to the quasi-isometry property. Therefore, `f z` is not far
away from $f(c^-)$ and $f(c^+)$ (again by the quasi-isometry property). Since the distance from
these points to `pi_z` is controlled (by `D + L`), we get a good control on `dist (f z) pi_z`, as
desired.

2.2 The interesting case is when $dm$ and $dM$ are both > `D`. Assume also for instance $dm \geq
dM$, as the other case is analogous. We will construct two points `f v` and `f x` with
`um ≤ v ≤ x ≤ y^-` with the following property:
\begin{equation}
\label{eq:xvK}
  K₁ e^{K₂ d(f(v), H)} \leq x-v,
\end{equation}
where `K₁` and `K₂` are some explicit constants (depending on `Λ`, `δ`, `L` and `D`).
Let us show how this will conclude the proof. The distance from `f v` to $f(c^+)$ is at most
$d(f(v),H) + L + dM \leq 3 d(f(v), H)$. Therefore, $c^+ - v$ is also controlled by $K' d(f(v), H)$
by the quasi-isometry property. This gives
\begin{align*}
  K &\leq K (x - v) e^{-K (c^+ - v)} \leq (e^{K (x-v)} - 1) \cdot e^{-K(c^+ - v)}
    \\& = e^{-K (c^+ - x)} - e^{-K (c^+ - v)}
    \leq e^{-K(c^+ - x)} - e^{-K (uM - um)}.
\end{align*}
This shows that, when one goes from the original quasi-geodesic $f([um, uM])$ to the restricted
quasi-geodesic $f([x, c^+])$, the quantity $e^{-K \cdot}$ decreases by a fixed amount. In particular,
this process can only happen a uniformly bounded number of times, say `n`.

Let `G'` be a geodesic between `f x` and $f(c^+)$. One checks geometrically that $d(f(z), G) \leq
d(f(z), G') + (L + O(\delta))$, as both projections of `f x` and $f(c^+)$ on $H$ are within
distance `L` of `pi_z`. Iterating the process `n` times, one gets finally $d(f(z), G) \leq O(1) + n
(L + O(\delta))$. This is the desired bound for `dist (f z) G`.

To complete the proof, it remains to construct the points `f v` and `f x` satisfying~\eqref{eq:xvK}.
This will be done through an inductive process.

Assume first that there is a point `f v` whose projection on `H` is close to the projection of
$f um$, and with `dist (f v) H ≤ 2 dm`. Then the projections of `f v` and $f ym$ are far away
(at distance at least $L + O(\delta)$). Since the portion of `f` between `v` and $y^-$ is everywhere
at distance at least $dm$ of `H`, the projection on `H` contracts by a factor $e^{-dm}$. It
follows that this portion of `f` has length at least $e^{dm} \cdot (L+O(\delta))$. Therefore, by
the quasi-isometry property, one gets $x - v \geq K e^{dm}$. On the other hand, `dist v H` is
bounded above by $2 dm$ by assumption. This gives the desired inequality~\eqref{eq:xvK} with $x =
y^-$.

Otherwise, all points `f v` whose projection on `H` is close to the projection of $f um$ are such
that $d(f(v), H) \geq 2 dm$. Consider `f w₁` a point whose projection on `H` is at distance
roughly `10 * δ` of the projection of $f um$. Let `V₁` be the set of points at distance at
most $dm$ of `H`, i.e., the $d_1$-neighborhood of `H`. Then the distance between the projections of
$f um$ and `f w₁` on `V₁` is very large (are there is an additional big contraction to go from
`V₁` to `H`). And moreover all the intermediate points `f v` are at distance at least $2 dm$ of
`H`, and therefore at distance at least $dm$ of `H`. Then one can play the same game as in the
first case, where $y^-$ replaced by `w₁` and `H` replaced by `V₁`. If there is a point `f v`
whose projection on `V₁` is close to the projection of $f um$, then the pair of points `v` and
`x = w₁` works. Otherwise, one lifts everything to `V₂`, the neighborhood of size $2dm$ of `V₁`,
and one argues again in the same way.

The induction goes on like this until one finds a suitable pair of points. The process has indeed to
stop at one time, as it can only go on while $f um$ is outside of `V k`, the $(2^k-1) dm$
neighborhood of `H`). This concludes the sketch of the proof, modulo the adjustment of constants.

Comments on the formalization below:
* The proof is written as an induction on `uM - um`. This makes it possible to either prove the
  bound directly (in the cases 1 and 2.1 above), or to use the bound on $d(z, G')$ in case 2.2
  using the induction assumption, and conclude the proof. Of course, $uM - um$ is not
  integer-valued, but in the reduction to `G'` it decays by a fixed amount, so this is a so-called
  "well-founded induction."
* The main difficulty in the proof is to construct the pair `(v, x)` in case 2.2. This is again
  written as an induction over `k`: either the required bound is true, or one can find a point `f w`
  whose projection on `V k` is far enough from the projection of $f um$. Then, either one can use
  this point to prove the bound, or one can construct a point with the same property with respect to
  `V (k+1)`, concluding the induction.
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
  freely, and have been chosen to get the best possible constant in the end. -/

variable {X : Type*} [MetricSpace X] [GromovHyperbolicSpace X] [GeodesicSpace X]

open GromovHyperbolicSpace

#time
set_option maxHeartbeats 1000000 in
/-- We prove that, for any pair of points to the left and to the right of `f z`, the distance
from `f z` to a geodesic between these points is controlled. We prove this by reducing to a
closer pair of points, i.e., this is an inductive argument over real numbers. It is "well-founded"
because in our reduction step the new pair of points is always significantly closer
than the initial one, at least by an amount `δ / Λ`.

The main inductive bound that we will prove is the following. In this bound, the first term is
what comes from the trivial cases 1 and 2.1 in the description of the proof before the statement
of the theorem, while the most interesting term is the second term, corresponding to the induction
per se. -/
lemma Morse_Gromov_theorem_aux0
    {f : ℝ → X} {um uM : ℝ}
    (hf : ContinuousOn f (Icc um uM))
    {Λ C : ℝ} (hf' : QuasiIsometryOn Λ C (Icc um uM) f)
    (h_um_uM : um ≤ uM)
    {z : ℝ} (hz : z ∈ Icc um uM)
    {δ : ℝ} (hδ : δ > deltaG X) :
    /- We give their values to the parameters `L`, `D` and `α` that we will use in the proof.
    We also define two constants `K` and `Kmult` that appear in the precise formulation of the
    bounds. Their values have no precise meaning, they are just the outcome of the computation. -/
    let α : ℝ := 12/100
    let L : ℝ := 18 * δ
    let D : ℝ := 55 * δ
    let K : ℝ := α * log 2 / (5 * (4 + (L + 2 * δ)/D) * δ * Λ)
    let Kmult : ℝ := ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp (1/2 * log 2)) * Λ * exp (- ((1 - α) * D * log 2 / (5 * δ))) / K)
    gromovProductAt (f z) (f um) (f uM)
      ≤ Λ^2 * (D + (3/2) * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (uM - um))) := by
  have hC := hf'.C_nonneg
  have := hf'.one_le_lambda
  have : Inhabited X := ⟨f 0⟩
  have hδ₀ : 0 < δ := by linarith only [hδ, delta_nonneg X]
  intro α L D K Kmult

  have : 0 < K := by ring_nf; positivity
  have : 1 ≤ Λ ^ 2 := by nlinarith only [hf'.one_le_lambda]
  have : Kmult > 0 := by ring_nf; positivity

  have : 0 ≤ uM - um := by linarith only [h_um_uM]
  by_cases hz_um_uM_L : gromovProductAt (f z) (f um) (f uM) ≤ L
  · /- If `f z` is already close to the geodesic, there is nothing to do, and we do not need
    the induction assumption. This is case 1 in the description above. -/
    calc gromovProductAt (f z) (f um) (f uM) ≤ L := hz_um_uM_L
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
  let m := {(f um)‒(f uM)}.param (f um) (gromovProductAt (f um) (f z) (f uM))

  let H : Set X := {(f z)‒m}
  let pi_z := H.param (f z) (gromovProductAt (f z) (f um) (f uM))
  have h_H : GeodesicSegmentBetween H (f z) m := [(f z)‒m]
  have h_H'' : GeodesicSegment H := ⟨_, _, h_H⟩
  have h_H' : pi_z ∈ H ∧ m ∈ H ∧ f z ∈ H := ⟨h_H.param_in_segment, h_H.right_mem, h_H.left_mem⟩
  have H_closure: closure H = H := by rw [h_H.isClosed.closure_eq]
  have Dpi_z : dist (f z) pi_z = gromovProductAt (f z) (f um) (f uM) := by
    dsimp [pi_z, H]
    apply h_H.param6
    refine ⟨gromovProductAt_nonneg (f z) (f um) (f uM), ?_⟩
    calc gromovProductAt (f z) (f um) (f uM) ≤ infDist (f z) {(f um)‒(f uM)} := by
          apply gromovProductAt_le_infDist [(f um)‒(f uM)]
      _ ≤ dist (f z) m := by
          apply infDist_le_dist_of_mem
          apply [(f um)‒(f uM)].param3
          simp

  -- Introduce the notation `p` for some projection on the geodesic `H`.
  have H_nonempty (r : ℝ) : (projSet (f r) H).Nonempty :=
    projSet_nonempty_of_compact h_H.isCompact h_H.nonempty _
  choose p hp using H_nonempty
  have pH (r : ℝ) : p r ∈ H := (hp r).1
  have pz : p z = f z := by simpa [distproj_self h_H'.2.2] using hp z

  /- The projection of `f um` on `H` is close to `pi_z` (but it does not have to be exactly
  `pi_z`). It is between `pi_z` and `m`. -/
  -- On `H`, the point `pi_z` lies between `p um` and `f z`
  have Dum : dist (p um) (f z) = dist (p um) pi_z + dist pi_z (f z) := by
    have := calc dist (f um) (f z) ≤ dist (f um) (p um) + dist (p um) (f z) := dist_triangle ..
      _ ≤ dist (f um) m + dist (p um) (f z) := by
        gcongr
        exact projSet_dist_le h_H'.2.1 (hp um)
      _ = gromovProductAt (f um) (f z) (f uM) + dist (p um) (f z) := by
        simp [m]
        apply [f um‒f uM].param6
        refine ⟨gromovProductAt_nonneg (f um) (f z) (f uM), ?_⟩ -- TODO positivity extension
        exact (gromovProductAt_le_dist _ _ _).2
    have A : gromovProductAt (f z) (f um) (f uM) ≤ dist (p um) (f z) := by
      dsimp [gromovProductAt] at this ⊢
      simp only [dist_comm] at this ⊢
      linarith only [this]
    apply le_antisymm
    · exact dist_triangle ..
    · have :=
      calc dist (p um) pi_z = |dist (p um) (f z) - dist pi_z (f z)| :=
            h_H.dist_along_wrt_endpoint (pH _) h_H'.1
        _ = dist (p um) (f z) - dist pi_z (f z) := by
          simp only [dist_comm] at Dpi_z A ⊢
          rw [Dpi_z, abs_of_nonneg]
          linarith only [A]
      linarith only [this]

  -- Choose a point `f ym` whose projection on `H` is roughly at distance `L` of `pi_z`.
  obtain ⟨ym, hym⟩ : ∃ ym ∈ Icc um z,
      (dist (p um) (p ym) ∈ Icc ((L + dist pi_z (p um)) - 4 * δ - 2 * 0) (L + dist pi_z (p um)))
                    ∧ (∀ r ∈ Icc um ym, dist (p um) (p r) ≤ L + dist pi_z (p um)) := by
    refine quasi_convex_projection_small_gaps (f := f) (G := H) ?_ hz.1 ?_ (fun t _ ↦ hp t) hδ ?_
    · exact hf.mono (Icc_subset_Icc (by rfl) hz.2)
    · exact h_H''.quasiconvex
    · refine ⟨?_, ?_⟩
      · dsimp [L]
        linarith only [hδ₀, @dist_nonneg _ _ pi_z (p um)]
      · simp only [dist_comm, pz] at Dum Dpi_z hz_um_uM_L ⊢
        linarith only [Dum, hz_um_uM_L, Dpi_z]
  have hym_dist : L - 4 * δ ≤ dist (p um) (p ym) := by
    have : 0 ≤ dist pi_z (p um) := dist_nonneg
    linarith only [hym.2.1.1, this]
  have h_um_ym_subset : Icc um ym ⊆ Icc um uM := Icc_subset_Icc (by rfl) (hym.1.2.trans hz.2)

  /- Choose a point `cm` between `f um` and `f ym` realizing the minimal distance to `H`.
  Call this distance `dm`. -/
  obtain ⟨closestm, hclosestm⟩ :
      ∃ closestm ∈ Icc um ym, ∀ v ∈ Icc um ym, infDist (f closestm) H ≤ infDist (f v) H := by
    have : ContinuousOn (fun r ↦ infDist (f r) H) (Icc um ym) :=
      continuous_infDist_pt H |>.comp_continuousOn (hf.mono h_um_ym_subset)
    refine IsCompact.exists_isMinOn ?_ ?_ this
    · exact isCompact_Icc
    · rw [nonempty_Icc]
      exact hym.1.1
  let dm : ℝ := infDist (f closestm) H
  have dm_nonneg : 0 ≤ dm := infDist_nonneg

  -- Same things but in the interval $[z, uM]$.
  have I : dist (f um) m + dist m (f uM) = dist (f um) (f uM)
            ∧ dist (f um) m = gromovProductAt (f um) (f z) (f uM) := by
    constructor
    · apply [(f um)‒(f uM)].dist_eq
      apply [(f um)‒(f uM)].param3
      simp
    · apply [(f um)‒(f uM)].param6
      simp
  -- On `H`, the point `pi_z` lies between `p uM` and `f z`
  have DuM : dist (p uM) (f z) = dist (p uM) pi_z + dist pi_z (f z) := by
    have := calc dist (f uM) (f z) ≤ dist (f uM) (p uM) + dist (p uM) (f z) := dist_triangle ..
      _ ≤ dist (f uM) m + dist (p uM) (f z) := by
        gcongr
        exact projSet_dist_le h_H'.2.1 (hp uM)
      _ = gromovProductAt (f uM) (f z) (f um) + dist (p uM) (f z) := by
        have h₁ := gromovProductAt_add (f um) (f uM) (f z)
        have h₂ := I.1
        have h₃ := I.2
        simp only [dist_comm, gromovProductAt_commute] at h₁ h₂ h₃ ⊢
        linarith only [h₁, h₂, h₃]
    have A : gromovProductAt (f z) (f um) (f uM) ≤ dist (p uM) (f z) := by
      dsimp [gromovProductAt] at this ⊢
      simp only [dist_comm] at this ⊢
      linarith only [this]
    apply le_antisymm
    · exact dist_triangle ..
    · have :=
      calc dist (p uM) pi_z = |dist (p uM) (f z) - dist pi_z (f z)| :=
          h_H.dist_along_wrt_endpoint (pH _) h_H'.1
        _ = dist (p uM) (f z) - dist pi_z (f z) := by
          simp only [dist_comm] at Dpi_z A ⊢
          rw [Dpi_z, abs_of_nonneg]
          linarith only [A]
      linarith only [this]

  -- Choose a point `f yM` whose projection on `H` is roughly at distance `L` of `pi_z`.
  obtain ⟨yM, hyM⟩ : ∃ yM ∈ Icc z uM,
      (dist (p uM) (p yM) ∈ Icc ((L + dist pi_z (p uM)) - 4 * δ - 2 * 0) (L + dist pi_z (p uM)))
                    ∧ (∀ r ∈ Icc yM uM, dist (p uM) (p r) ≤ L + dist pi_z (p uM)) := by
    refine quasi_convex_projection_small_gaps' (f := f) (G := H) ?_ hz.2 ?_ (fun t _ ↦ hp t) hδ ?_
    · exact hf.mono (Icc_subset_Icc hz.1 (le_refl _))
    · exact h_H''.quasiconvex
    · refine ⟨?_, ?_⟩
      · dsimp [L]
        linarith only [hδ₀, @dist_nonneg _ _ pi_z (p uM)]
      · simp only [dist_comm, pz] at DuM Dpi_z hz_um_uM_L ⊢
        linarith only [DuM, hz_um_uM_L, Dpi_z]
  have h_yM_uM_subset : Icc yM uM ⊆ Icc um uM := Icc_subset_Icc (hz.1.trans hyM.1.1) (le_refl _)
  have hyM_dist : L - 4 * δ ≤ dist (p uM) (p yM) := by
    have : 0 ≤ dist pi_z (p uM) := dist_nonneg
    linarith only [hyM.2.1.1, this]
  have : ContinuousOn (fun r ↦ infDist (f r) H) (Icc yM uM) :=
    continuous_infDist_pt H |>.comp_continuousOn (hf.mono h_yM_uM_subset)

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

  set G := gromovProductAt (f z) (f um) (f uM)
  have h_fz_m_G : dist (f z) m ≤ G + 2 * δ := by
    calc _ ≤ G + 2 * deltaG X := dist_triangle_side_middle _ [(f um)‒(f uM)]
      _ ≤ G + 2 * δ := by rel [hδ]
  clear_value m

  /- Points between `f um` and `f ym`, or between `f yM` and `f uM`, project onto `H` within `L` of
  (or beyond) the Gromov product `G` from `f z`, by construction. -/
  have P {x : ℝ} (hx : x ∈ Icc um ym ∪ Icc yM uM) : G ≤ dist (f z) (p x) + L  := by
    have h₁ := h_H.dist_eq (pH x)
    obtain hx | hx := hx
    · have h₂ := h_H.dist_eq (pH um)
      have h₃ := hym.2.2 x hx
      have h₄ := dist_triangle m (p um) (p x)
      simp only [dist_comm] at Dum h₁ h₂ h₃ h₄ Dpi_z ⊢
      linarith only [Dum, h₁, h₂, h₃, h₄, Dpi_z]
    · have h₂ := h_H.dist_eq (pH uM)
      have h₃ := hyM.2.2 x hx
      have h₄ := dist_triangle m (p uM) (p x)
      simp only [dist_comm] at DuM h₁ h₂ h₃ h₄ Dpi_z ⊢
      linarith only [DuM, h₁, h₂, h₃, h₄, Dpi_z]
  replace hym := hym.1
  replace hyM := hyM.1
  clear_value pi_z
  clear Dum DuM Dpi_z I

  /- Auxiliary fact for later use:
  The distance between two points in $[um, ym]$ and $[yM, uM]$ can be controlled using
  the distances of their images under `f` to `H`, thanks to the quasi-isometry property. -/
  have hD {rm rM} (hrm : rm ∈ Icc um ym) (hrM : rM ∈ Icc yM uM) :
      |rm - rM| ≤ Λ * (infDist (f rm) H + (L + C + 2 * δ) + infDist (f rM) H) := by
    have := -- `*`
    calc dist (p rm) (p rM) = |dist (p rm) (f z) - dist (p rM) (f z)| :=
          h_H.dist_along_wrt_endpoint (pH _) (pH _)
      _ ≤ L + (dist (f z) m  - G) := by
          rw [abs_le]
          have h₁ := P (Or.inl hrm)
          have h₂ := P (Or.inr hrM)
          have h₄ : dist (f z) (p rm) ≤ dist (f z) m := h_H.dist_le (pH _)
          have h₃ : dist (f z) (p rM) ≤ dist (f z) m := h_H.dist_le (pH _)
          simp only [dist_comm] at h₁ h₂ h₃ h₄ ⊢
          constructor
          · linarith only [h₁, h₃]
          · linarith only [h₂, h₄]
      _ ≤ L + 2 * δ := by linarith only [h_fz_m_G]
    have :=
    calc (1/Λ) * |rm - rM| - C ≤ dist (f rm) (f rM) :=
          hf'.lower_bound (h_um_ym_subset hrm) (h_yM_uM_subset hrM)
      _ ≤ dist (f rm) (p rm) + dist (p rm) (p rM) + dist (p rM) (f rM) := dist_triangle4 ..
      _ ≤ infDist (f rm) H + (L + 2 * δ) + infDist (f rM) H := by
          have h₁ := (hp rm).2
          have h₂ := (hp rM).2
          simp only [dist_comm] at h₁ h₂ this ⊢
          linarith only [h₁, h₂, this]
    calc |rm - rM| = Λ * ((1/Λ) * |rm - rM| - C) + Λ * C := by field_simp
      _ ≤ Λ * (infDist (f rm) H + (L + 2 * δ) + infDist (f rM) H) + Λ * C := by gcongr
      _ = _ := by ring
  clear h_fz_m_G

  /- Auxiliary fact for later use in the inductive argument: the distance from `f z` to the
  geodesic `{(f um)‒(f uM)}` is controlled by the distance from `f z` to any
  intermediate geodesic between points in $f[um, ym]$ and $f[yM, uM]$, up to a constant
  essentially given by `L`. This is a variation around Lemma 5 in~\<^cite>\<open>"shchur"\<close>. -/
  have Rec {rm rM} (hrm : rm ∈ Icc um ym) (hrM : rM ∈ Icc yM uM) :
      gromovProductAt (f z) (f um) (f uM) ≤ gromovProductAt (f z) (f rm) (f rM) + (L + 4 * δ) := by
    have h₃m := P (Or.inl hrm)
    have h₃M := P (Or.inr hrM)
    have A : G - L - 2 * deltaG X ≤ gromovProductAt (f z) (f rm) (p rm) := by
      have h₁ : dist (f rm) (p rm) + dist (p rm) (f z) ≤ dist (f rm) (f z) + 4 * deltaG X :=
        dist_along_geodesic h_H'' (hp _) h_H'.2.2
      simp only [gromovProductAt, dist_comm] at h₁ h₃m ⊢
      linarith only [h₁, h₃m]
    have B : G - L - 2 * deltaG X ≤ gromovProductAt (f z) (p rM) (f rM) := by
      have h₁ : dist (f rM) (p rM) + dist (p rM) (f z) ≤ dist (f rM) (f z) + 4 * deltaG X :=
        dist_along_geodesic h_H'' (hp _) h_H'.2.2
      simp only [gromovProductAt, dist_comm] at h₁ h₃M ⊢
      linarith only [h₁, h₃M]
    have C : G - L - 2 * deltaG X ≤ gromovProductAt (f z) (p rm) (p rM) := by
      by_cases h : dist (f z) (p rm) ≤ dist (f z) (p rM)
      · have h₁ :=
        calc dist (p rm) (p rM) = |dist (f z) (p rm) - dist (f z) (p rM)| := by
              have := h_H.dist_along_wrt_endpoint (pH rm) (pH rM)
              simp only [dist_comm] at this ⊢
              linarith only [this]
          _ = dist (f z) (p rM) - dist (f z) (p rm) := by
              rw [abs_of_nonpos]
              · ring
              · linarith only [h]
        simp only [gromovProductAt, dist_comm] at h h₁ h₃m ⊢
        linarith only [h, h₁, h₃m, delta_nonneg X]
      · have h₁ :=
        calc dist (p rm) (p rM) = |dist (f z) (p rm) - dist (f z) (p rM)| := by
              have :=  h_H.dist_along_wrt_endpoint (pH rm) (pH rM)
              simp only [dist_comm] at this ⊢
              linarith only [this]
          _ = dist (f z) (p rm) - dist (f z) (p rM) := by
              rw [abs_of_nonneg]
              linarith only [h]
        simp only [gromovProductAt, dist_comm] at h h₁ h₃M ⊢
        linarith only [h, h₁, h₃M, delta_nonneg X]
    have :=
    calc gromovProductAt (f z) (f um) (f uM) - L - 2 * deltaG X
        ≤ min (gromovProductAt (f z) (f rm) (p rm))
            (min (gromovProductAt (f z) (p rm) (p rM))
              (gromovProductAt (f z) (p rM) (f rM))) := by
          simp only [le_min_iff]
          exact ⟨A, C, B⟩
      _ ≤ gromovProductAt (f z) (f rm) (f rM) + 2 * deltaG X :=
            hyperb_ineq_4_points' (f z) (f rm) (p rm) (p rM) (f rM)
    linarith only [this, hδ]
  clear P h_H'

  /- We have proved the basic facts we will need in the main argument. This argument starts
  here. It is divided in several cases. -/
  by_cases h : (dm ≤ D + 4 * C ∧ dM ≤ D + 4 * C)
  · obtain ⟨hdm, hdM⟩ : (dm ≤ D + 4 * C ∧ dM ≤ D + 4 * C) := h

  /- Case 2.1 of the description before the statement: there are points in $f[um, ym]$ and
  in $f[yM, uM]$ which are close to `H`. Then one can conclude directly, without relying
  on the inductive argument, thanks to the quasi-isometry property. -/
    have I : gromovProductAt (f z) (f closestm) (f closestM) ≤ Λ^2 * (D + L / 2 + δ + 11/2 * C) - 6 * δ := by
      have H :=
      calc dist (f closestm) (f z) + dist (f z) (f (closestM))
            ≤ (Λ * |closestm - z| + C) + (Λ * |z - closestM| + C) := by
              rw [← Real.dist_eq]
              gcongr
              · exact hf'.upper_bound (h_um_ym_subset hclosestm.1) hz
              · exact hf'.upper_bound hz (h_yM_uM_subset hclosestM.1)
          _ = Λ * |closestm - closestM| + 1 * 2 * C := by
              have h₁ := hclosestm.1.2
              have h₂ := hclosestM.1.1
              have h₃ := hym.2
              have h₄ := hyM.1
              rw [abs_of_nonpos, abs_of_nonpos, abs_of_nonpos] <;> linarith only [h₁, h₂, h₃, h₄]
      by_cases h_closest : dist (f closestm) (f closestM) ≤ 12 * δ
      · have :=
        calc 2 * gromovProductAt (f z) (f closestm) (f closestM)
            ≤ dist (f closestm) (f z) + dist (f z) (f (closestM)) := by
              dsimp [gromovProductAt]
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
              exact hf'.lower_bound (h_um_ym_subset hclosestm.1) (h_yM_uM_subset hclosestM.1)
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
        simp only [gromovProductAt, dist_comm] at this h_closest ⊢
        linarith only [this, h_closest]
    calc gromovProductAt (f z) (f um) (f uM)
        ≤ gromovProductAt (f z) (f closestm) (f closestM) + 1 * L + 4 * δ + 0 * (1 - exp (- K * (uM - um))) := by
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
  let QC : ℕ → ℝ := fun k ↦ if k = 0 then 0 else 8 * δ
  have QC_nonneg (k : ℕ) : 0 ≤ QC k := by dsimp [QC]; split <;> positivity

  obtain I₂ | I₂ := le_or_gt dM dm
  · have I₁ : dm ≥ D + 4 * C := by
      rw [not_and_or] at h
      push_neg at h
      obtain I₁ | I₁ := h <;> linarith only [I₁, I₂]

    have : 0 < dm := by dsimp [D] at I₁; linarith only [I₁, hC, hδ₀]
    let V : ℕ → Set X := fun k ↦ cthickening ((2^k - 1) * dm) H
    have Q (k : ℕ) : Quasiconvex (0 + 8 * deltaG X) (V k) := by
      apply h_H''.quasiconvex.cthickening
      have : 1 ≤ (2:ℝ) ^ k := one_le_pow_of_one_le (by norm_num) k
      have : 0 ≤ (2:ℝ) ^ k - 1 := by linarith only [this]
      positivity
    have V_quasiconvex (k : ℕ) : Quasiconvex (QC k) (V k) := by
      dsimp [QC]
      split_ifs with h
      · simp only [h, pow_zero, sub_self, zero_mul, V, cthickening_zero]
        rw [H_closure]
        apply h_H''.quasiconvex
      · refine (Q k).mono ?_
        linarith only [hδ]

    -- Define `q k x` to be the projection of `f x` on `V k`.
    let q : ℕ → ℝ → X := fun k x ↦ {p x‒f x}.param (p x) ((2^k - 1) * dm)
    have hq0 (x : ℝ) : q 0 x = p x := by
      dsimp [q]
      convert [p x‒f x].param1
      simp

    -- We introduce a certain property of natural numbers `k` which will eventually let us select
    -- our endpoint `x`.
    let P (k : ℕ) := ∃ x ∈ Icc um ym, dist (q k um) (q k x) ≥ L - 4 * δ + 7 * QC k
      ∧ ∀ w ∈ Icc um x, dist (f w) (p w) ≥ (2^(k+1)-1) * dm

    /- The property holds for `k = 0`, i.e. there is a point far enough from `q 0 um` on `H`. This
    is just the right endpoint `ym`, by construction. -/
    have hP₀ : P 0 := by
      refine ⟨ym, ?_, ?_, ?_⟩
      · simp [hym.1]
      · simp only [hq0, QC, reduceIte]
        linarith only [hym_dist]
      · intro w hw
        calc _ = _ := by ring
          _ ≤ _ := hclosestm.2 w hw
          _ ≤ _ := infDist_le_dist_of_mem (pH _)

    /- The property fails for `k` sufficiently large, by considering the left endpoint `um`. -/
    have hP : ∀ᶠ k in atTop, ¬ P k := by
      have H : ∀ᶠ k in atTop, dist (f um) (p um) < (2 ^ (k + 1) + -1) * dm := by
        refine tendsto_atTop_add_const_right _ (-1:ℝ)
          (tendsto_pow_atTop_atTop_of_one_lt (r := (2:ℝ)) ?_)
          |>.atTop_mul_const (r := dm) ?_
          |>.comp (tendsto_add_atTop_nat 1)
          |>.eventually_gt_atTop _
        · norm_num
        · positivity
      filter_upwards [H] with k hk
      dsimp [P]
      push_neg
      intro t ht _
      exact ⟨um, ⟨by rfl, ht.1⟩, hk⟩

    -- Thus there exists a natural number `k` such that `P k` holds and `P (k + 1)` doesn't.
    -- Select the witness `x` for this `k`.
    obtain ⟨k, hk₁, hk₂⟩ : ∃ k, P k ∧ ¬ P (k + 1) := by -- there should be a lemma for this!
      by_contra! h
      obtain ⟨k, hk⟩ := hP.exists
      exact hk (Nat.rec hP₀ h k)
    obtain ⟨x, hx₁, hx₃, hx₂⟩ :
      ∃ x ∈ Icc um ym, L - 4 * δ + 7 * QC k ≤ dist (q k um) (q k x)
        ∧ (∀ w, w ∈ Icc um x → dist (f w) (p w) ≥ (2^(k+1)-1) * dm) := hk₁

    -- FIXME these are basically `aux`, deduplicate
    have h_pow : (1:ℝ) ≤ 2 ^ k := one_le_pow_of_one_le (by norm_num) k
    have h_pow' : 0 ≤ (2:ℝ) ^ k - 1 := by linarith only [h_pow]
    have h_pow'' : (1:ℝ) ≤ 2 ^ (k + 1) := one_le_pow_of_one_le (by norm_num) _
    have h_pow''' : 0 ≤ (2:ℝ) ^ (k + 1) - 1 := by linarith only [h_pow'']
    have hdm_mul : 0 ≤ dm * 2 ^ k := by positivity
    have H₁ : (2 ^ k - 1) * dm ≤ (2 ^ (k + 1) - 1) * dm := by ring_nf; linarith only [hdm_mul]

    -- Some auxiliary technical inequalities to be used later on.
    have aux : (2 ^ k - 1) * dm ≤ (2*2^k-1) * dm ∧ 0 ≤ 2 * 2 ^ k - (1:ℝ) ∧ dm ≤ dm * 2 ^ k := by
      refine ⟨?_, ?_, ?_⟩
      · convert H₁ using 1
        ring
      · convert h_pow''' using 1
        ring
      · calc _ = dm * 1 := by ring
          _ ≤ _ := by gcongr
    have aux2 : L + C + 2 * δ ≤ ((L + 2 * δ)/D) * dm := by
      have h₁ :=
      calc L + C = (L/D) * (D + (D/L) * C) := by field_simp; ring
        _ ≤ (L/D) * (D + 4 * C) := by
            gcongr
            rw [div_le_iff]
            · dsimp [D, L]
              linarith only [hδ₀]
            positivity
        _ ≤ (L/D) * dm := by gcongr
      have h₂ :=
      calc 2 * δ = (2 * δ) / D * D := by field_simp
        _ ≤ (2 * δ)/D * dm := by
            gcongr
            linarith only [I₁, hC]
      rw [add_div, add_mul]
      linarith only [h₁, h₂]
    have aux3 : (1-α) * D + α * 2^k * dm ≤ dm * 2^k - C/2 - QC k := by
      dsimp [QC]
      split_ifs with h
      · simp only [h, pow_zero]
        dsimp [α, D] at I₁ ⊢
        linarith only [I₁, hδ₀, hC]
      have :=
      calc C/2 + 8 * δ + (1-α) * D
          ≤ 2 * (1-α) * dm := by
            dsimp [α, D] at I₁ ⊢
            linarith only [I₁, hδ₀, hC]
        _ = 2 ^ 1 * (1-α) * dm := by ring
        _ ≤ 2^k * (1-α) * dm := by
            gcongr
            · norm_num
            · show 0 < k
              positivity
      linarith only [this]

    have proj_mem {r : ℝ} (hr : r ∈ Icc um x) : q k r ∈ projSet (f r) (V k) := by
      dsimp [q, V]
      convert [p r‒f r].projSet_thickening' (E := dist (p r) (f r)) (hp _) ?_ ?_ (by rfl) using 2
      · rw [[p r‒f r].param2]
      · positivity
      · rw [dist_comm]
        exact le_trans H₁ (hx₂ _ hr)

    have h_um_x_subset : Icc um x ⊆ Icc um uM := by
      rw [Icc_subset_Icc_iff] at h_um_ym_subset ⊢
      · exact ⟨h_um_ym_subset.1, hx₁.2.trans h_um_ym_subset.2⟩
      · exact hx₁.1
      · exact hym.1
    /- Construct a point `w` such that its projection on `V k` is O(δ)-close to that of `um`
    and therefore far away from that of `x`. This is just the intermediate value theorem
    (with some care as the closest point projection is not continuous). -/
    obtain ⟨w, hw₁, hw₂, hw₃⟩ : ∃ w ∈ Icc um x,
        dist (q k um) (q k w) ∈ Icc ((9 * δ + 4 * QC k) - 4 * δ - 2 * QC k) (9 * δ + 4 * QC k)
        ∧ (∀ v ∈ Icc um w, dist (q k um) (q k v) ≤ 9 * δ + 4 * QC k) := by
      apply quasi_convex_projection_small_gaps (f := f) (G := V k)
      · exact hf.mono h_um_x_subset
      · exact hx₁.1
      · exact V_quasiconvex _
      · intro w hw
        apply proj_mem hw
      · exact hδ
      · have := QC_nonneg k
        refine ⟨?_, le_trans ?_ hx₃⟩
        · ring_nf
          linarith only [this, hδ₀]
        · dsimp [L]
          ring_nf
          linarith only [this, hδ₀]

    /- The projections of `um` and `w` onto `V (k + 1)` are necessarily at least O(δ) apart. -/
    have : dist (q (k + 1) um) (q (k + 1) w) ≥ L - 4 * δ + 7 * QC (k + 1) := by
      have h₁ : dist (q k um) (q (k+1) um) = 2^k * dm := by
        dsimp [q]
        rw [[p um‒f um].param7]
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
        rw [[p w‒f w].param7]
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
      have i : q k um ∈ projSet (q (k+1) um) (V k) := by
        refine [p um‒f um].projSet_thickening' (hp _) ?_ H₁ ?_
        · positivity
        · rw [dist_comm]
          refine le_trans ?_ (hx₂ _ ⟨by rfl, hx₁.1⟩).le
          rw [← sub_nonneg]
          ring_nf
          positivity
      have j : q k w ∈ projSet (q (k+1) w) (V k) := by
        refine [p w‒f w].projSet_thickening' (hp _) ?_ H₁ ?_
        · positivity
        · rw [dist_comm]
          refine le_trans ?_ (hx₂ _ hw₁).le
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

    /- So, since `k` is chosen so that `P (k + 1)` is known to be false, this implies there is a
    good point `v` between `um` and `w`. This is the heart of the argument: we will now show that
    the desired inequality for the Gromov product holds. -/
    dsimp [P] at hk₂
    push_neg at hk₂
    obtain ⟨v, hv₁, hv₂⟩ : ∃ v ∈ Icc um w, dist (f v) (p v) < (2^(k+2)-1) * dm :=
      hk₂ w ⟨hw₁.1, hw₁.2.trans hx₁.2⟩ this

    -- Auxiliary basic fact to be used later on.
    have aux4 {r : ℝ} (hr : r ∈ Icc v x) : dm * 2 ^ k ≤ infDist (f r) (V k) := by
      have hr : r ∈ Icc um x := ⟨hv₁.1.trans hr.1, hr.2⟩
      have h₁ :=
      calc infDist (f r) (V k)
          = dist ({p r‒f r}.param (p r) (dist (p r) (f r)))
              ({p r‒f r}.param (p r) ((2 ^ k - 1) * dm)) := by
              rw [← (proj_mem hr).2]
              dsimp [q]
              rw [[p r‒f r].param2]
          _ = |dist (p r) (f r) - (2 ^ k - 1) * dm| := by
              apply [p r‒f r].param7
              · simpa using dist_nonneg
              refine ⟨by positivity, ?_⟩
              rw [dist_comm]
              exact le_trans H₁ (hx₂ _ hr)
          _ = dist (f r) (p r) - (2 ^ k - 1) * dm := by
              rw [dist_comm (p r), abs_of_nonneg]
              linarith only [hx₂ r hr, H₁]
      have h₂ : (2^(k+1) - 1) * dm ≤ dist (f r) (p r) := hx₂ _ hr
      ring_nf at h₂
      linarith only [h₁, h₂]

    /- Substep 1: We can control the distance from `f v` to `f closestM` in terms of the distance
    of the distance of `f v` to `H`, i.e., by `2^k * dm`. The same control follows
    for `closestM - v` thanks to the quasi-isometry property. Then, we massage this
    inequality to put it in the form we will need, as an upper bound on `(x-v) * exp (-2^k * dm)`. -/
    have :=
    calc |v - closestM| ≤ Λ * (infDist (f v) H + (L + C + 2 * δ) + infDist (f closestM) H) := by
          apply hD ⟨hv₁.1, ?_⟩ hclosestM.1
          linarith only [hv₁.2, hw₁.2, hx₁.2]
      _ ≤ Λ * ((2^(k+2)-1) * dm + (L + C + 2 * δ) + dM) := by
          gcongr
          rw [← (hp v).2]
          exact hv₂.le
      _ = Λ * ((2^(k+2)-1) * dm + 1 * (L + C + 2 * δ) + dM) := by ring
      _ ≤ Λ * ((2^(k+2)-1) * dm + 2^k * (((L + 2 * δ)/D) * dm) + dm) := by
          gcongr
      _ = Λ * 2^k * (4 + (L + 2 * δ)/D) * dm := by ring
    have : |v - closestM| / (Λ * (4 + (L + 2 * δ)/D)) ≤ 2^k * dm := by
      rw [div_le_iff]
      convert this using 1
      · ring
      · positivity
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
          linarith only [hv₁.2, hw₁.2, hx₁.2, hym.2, hyM.1, hclosestM.1.1]
    have : 0 ≤ x - v := by linarith only [hv₁.2, hw₁.2]
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
          · linarith only [hv₁.1, hclosestM.1.2]
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
          obtain rfl | hk := eq_or_ne k 0
          · have : dist (q 0 v) (q 0 x)
                ≤ max (5 * deltaG X)
                  ((4 * exp (1/2 * log 2)) * Λ * (x - v)
                  * exp (-(dm * 2^0 - C/2) * log 2 / (5 * δ))) := by
              apply geodesic_projection_exp_contracting (G := V 0) (f := f)
              · intro x1 x2 hx1 hx2
                apply hf'.upper_bound
                · exact ⟨by linarith only [hv₁.1, hx1.1],
                    by linarith only [hx1.2, hx₁.2, hym.2, hz.2]⟩
                · exact ⟨by linarith only [hv₁.1, hx2.1],
                    by linarith only [hx2.2, hx₁.2, hym.2, hz.2]⟩
              · exact hv₁.2.trans hw₁.2
              · simpa [hq0, V, H_closure] using hp v
              · simpa [hq0, V, H_closure] using hp x
              · intro t
                exact aux4
              · simp only [pow_zero]
                dsimp [D] at I₁
                linarith only [I₁, hC, hδ₀]
              · exact hδ
              · exact hC
              · positivity
              · simpa [V, H_closure] using h_H''
            simpa [hq0, QC] using this
          · have : dist (q k v) (q k x)
                ≤ 2 * QC k + 8 * δ + max (5 * deltaG X)
                  ((4 * exp (1/2 * log 2)) * Λ * (x - v) * exp (-(dm * 2^k - QC k -C/2) * log 2 / (5 * δ))) := by
              apply quasiconvex_projection_exp_contracting (G := V k) (f := f)
              · intro x1 x2 hx1 hx2
                apply hf'.upper_bound
                · exact ⟨by linarith only [hv₁.1, hx1.1],
                    by linarith only [hx1.2, hx₁.2, hym.2, hz.2]⟩
                · exact ⟨by linarith only [hv₁.1, hx2.1],
                    by linarith only [hx2.2, hx₁.2, hym.2, hz.2]⟩
              · exact hv₁.2.trans hw₁.2
              · apply proj_mem
                exact ⟨hv₁.1, hv₁.2.trans hw₁.2⟩
              · apply proj_mem
                exact ⟨hx₁.1, by rfl⟩
              · intro t
                exact aux4
              · dsimp [QC]
                rw [if_neg hk]
                dsimp [D] at I₁
                linarith only [hδ₀, hC, I₁, aux.2.2]
              · exact hδ
              · exact hC
              · positivity
              · apply V_quasiconvex
            refine le_trans this ?_
            simp only [if_neg hk, QC]
            ring_nf
            rfl

    have : L - 13 * δ ≤ max (5 * deltaG X)
      ((4 * exp (1/2 * log 2)) * Λ * (x - v) * exp (-(dm * 2^k - C/2 - QC k) * log 2 / (5 * δ))) := by
      linarith only [this]
    have A :=
    calc L - 13 * δ
        ≤ (4 * exp (1/2 * log 2)) * Λ * (x - v)
          * exp (-(dm * 2^k - C/2 - QC k) * log 2 / (5 * δ)) := by
          rw [le_max_iff] at this
          apply this.resolve_left
          push_neg
          dsimp [L]
          linarith only [hδ]
      /- We separate the exponential gain coming from the contraction into two parts, one
      to be spent to improve the constant, and one for the inductive argument. -/
      _ ≤ (4 * exp (1/2 * log 2)) * Λ * (x - v)
          * exp (-((1-α) * D + α * 2^k * dm) * log 2 / (5 * δ)) := by
          gcongr -- `aux3`
      _ = (4 * exp (1/2 * log 2)) * Λ * 1 * ((x - v)
          * (exp (-(1-α) * D * log 2 / (5 * δ)) * exp (-α * 2^k * dm * log 2 / (5 * δ)))) := by
          rw [← exp_add]
          ring_nf
      _ = (4 * exp (1/2 * log 2)) * Λ * exp (-((1-α) * D * log 2 / (5 * δ))) * ((x - v)
          * exp (-(α * (2^k * dm) * log 2 / (5 * δ)))) := by
          ring_nf
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
    calc (1/4) * δ / Λ
        ≤ - v + x := by linarith only [this]
      _ ≤ uM - um + x - closestM := by linarith only [hclosestM.1.2, hv₁.1]
    -- start to set up for the well-founded induction
    have h₂ : z ∈ Icc x closestM :=
      ⟨by linarith only [hx₁.2, hym.2], by linarith only [hyM.1, hclosestM.1.1]⟩
    have h₁ : x ≤ closestM := h₂.1.trans h₂.2
    have : Nat.floor (4 * Λ * |closestM - x| / δ) < Nat.floor (4 * Λ * |uM - um| / δ) := by
      calc Nat.floor (4 * Λ * |closestM - x| / δ) < Nat.floor (4 * Λ * |closestM - x| / δ + 1) := by
            rw [Nat.floor_add_one]
            · omega
            positivity
        _ ≤ Nat.floor (4 * Λ * |uM - um| / δ) := by
            gcongr
            rw [le_div_iff]
            rw [div_le_iff] at this
            field_simp
            rw [abs_of_nonneg, abs_of_nonneg]
            linarith only [this]
            · positivity
            · linarith only [h₁]
            all_goals positivity

    /- Conclusion of the proof: combine the lower bound of the second substep with
    the upper bound of the first substep to get a definite gain when one goes from
    the old geodesic to the new one. Then, apply the inductive assumption to the new one
    to conclude the desired inequality for the old one. -/
    have : 0 < (L - 13 * δ) := by
      dsimp [L]
      ring_nf
      positivity
    have H₂ :=
    calc L + 4 * δ = ((L + 4 * δ)/(L - 13 * δ)) * (L - 13 * δ) := by field_simp
      _ ≤ ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp (1/2 * log 2)) * Λ
          * exp (- ((1 - α) * D * log 2 / (5 * δ))) * ((x - v)
          * exp (- (α * (2 ^ k * dm) * log 2 / (5 * δ))))) := by rel [A]
      _ ≤ ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp (1/2 * log 2)) * Λ
          * exp (- ((1 - α) * D * log 2 / (5 * δ)))
          * ((exp (-K * (closestM - x)) - exp (-K * (uM - um)))/K)) := by rel [B]
      _ = Kmult * (exp (-K * (closestM - x)) - exp (-K * (uM - um))) := by
          dsimp [Kmult]
          ring

    calc gromovProductAt (f z) (f um) (f uM)
        ≤ gromovProductAt (f z) (f x) (f closestM) + (L + 4 * δ) := Rec hx₁ hclosestM.1
      _ ≤ (Λ ^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ
          + Kmult * (1 - exp (- K * (closestM - x))))
          + (Kmult * (exp (-K * (closestM - x)) - exp (-K * (uM-um)))) := by
          have h₃ : Icc x closestM ⊆ Icc um uM := by
            rw [Icc_subset_Icc_iff h₁]
            exact ⟨hx₁.1, hclosestM.1.2⟩
          have := Morse_Gromov_theorem_aux0 (hf.mono h₃) (hf'.mono h₃) h₁ h₂ hδ
          dsimp [D, K, Kmult, L] at this H₂ ⊢
          linarith only [this, H₂]
      _ = (Λ^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (uM - um)))) := by
          dsimp [K]
          ring
  -- end of the case where `D + 4 * C ≤ dm` and `dM ≤ dm`.

  /- This is the exact copy of the previous case, except that the roles of the points before
  and after `z` are exchanged. In a perfect world, one would use a lemma subsuming both cases,
  but in practice copy-paste seems to work better here as there are too many details to be
  changed regarding the direction of inequalities. -/
  · replace I₂ := I₂.le
    have I₁ : dM ≥ D + 4 * C := by
      rw [not_and_or] at h
      push_neg at h
      obtain I₁ | I₁ := h <;> linarith only [I₁, I₂]
    let V : ℕ → Set X := fun k ↦ cthickening ((2^k - 1) * dM) H
    have Q (k : ℕ) : Quasiconvex (0 + 8 * deltaG X) (V k) := by
      apply h_H''.quasiconvex.cthickening
      have : 1 ≤ (2:ℝ) ^ k := one_le_pow_of_one_le (by norm_num) k
      have : 0 ≤ (2:ℝ) ^ k - 1 := by linarith only [this]
      positivity
    have V_quasiconvex (k : ℕ) : Quasiconvex (QC k) (V k) := by
      dsimp [QC]
      split_ifs with h
      · simp only [h, pow_zero, sub_self, zero_mul, V, cthickening_zero]
        rw [H_closure]
        exact h_H''.quasiconvex
      · refine (Q k).mono ?_
        linarith only [hδ]
    have : 0 < dM := by dsimp [D] at I₁; linarith only [I₁, hC, hδ₀]

    -- Define `q k x` to be the projection of `f x` on `V k`.
    let q : ℕ → ℝ → X := fun k x ↦ {p x‒f x}.param (p x) ((2^k - 1) * dM)
    have hq0 (x : ℝ) : q 0 x = p x := by
      dsimp [q]
      convert [p x‒f x].param1
      simp

    -- The inductive argument
    have Ind_k (k : ℕ) :
        gromovProductAt (f z) (f um) (f uM)
          ≤ Λ^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (uM - um)))
        ∨ (∃ x ∈ Icc yM uM, (∀ w ∈ Icc x uM, dist (f w) (p w) ≥ (2^(k+1)-1) * dM)
            ∧ dist (q k uM) (q k x) ≥ L - 4 * δ + 7 * QC k) := by
      induction' k with k IH
      /- Base case: there is a point far enough from `q 0 uM` on `H`. This is just the point `yM`,
      by construction. -/
      · right
        refine ⟨yM, ?_, ?_, ?_⟩
        · simp [hyM.2]
        · intro w hw
          calc _ = _ := by ring
            _ ≤ _ := hclosestM.2 w hw
            _ ≤ _ := infDist_le_dist_of_mem (pH _)
        · simp only [hq0, QC, reduceIte]
          linarith only [hyM_dist]

      /- The induction. The inductive assumption claims that, either the desired inequality
      holds, or one can construct a point with good properties. If the desired inequality holds,
      there is nothing left to prove. Otherwise, we can start from this point at step `k`,
      say `x`, and either prove the desired inequality or construct a point with the good
      properties at step `k + 1`. -/
      by_cases h :
        gromovProductAt (f z) (f um) (f uM)
          ≤ Λ ^ 2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (uM - um)))
      · exact Or.inl h

      obtain ⟨x, hx₁, hx₂, hx₃⟩ :
        ∃ x ∈ Icc yM uM, (∀ w, w ∈ Icc x uM → dist (f w) (p w) ≥ (2^(k+1)-1) * dM)
          ∧ L - 4 * δ + 7 * QC k ≤ dist (q k uM) (q k x) :=
        IH.resolve_left h

      -- FIXME these are basically `aux`, deduplicate
      have h_pow : (1:ℝ) ≤ 2 ^ k := one_le_pow_of_one_le (by norm_num) k
      have h_pow' : 0 ≤ (2:ℝ) ^ k - 1 := by linarith only [h_pow]
      have h_pow'' : (1:ℝ) ≤ 2 ^ (k + 1) := one_le_pow_of_one_le (by norm_num) _
      have h_pow''' : 0 ≤ (2:ℝ) ^ (k + 1) - 1 := by linarith only [h_pow'']
      have hdM_mul : 0 ≤ dM * 2 ^ k := by positivity
      have H₁ : (2 ^ k - 1) * dM ≤ (2 ^ (k + 1) - 1) * dM := by ring_nf; linarith only [hdM_mul]

      -- Some auxiliary technical inequalities to be used later on.
      have aux : (2 ^ k - 1) * dM ≤ (2*2^k-1) * dM ∧ 0 ≤ 2 * 2 ^ k - (1:ℝ) ∧ dM ≤ dM * 2 ^ k := by
        refine ⟨?_, ?_, ?_⟩
        · convert H₁ using 1
          ring
        · convert h_pow''' using 1
          ring
        · calc _ = dM * 1 := by ring
            _ ≤ _ := by gcongr
      have aux2 : L + C + 2 * δ ≤ ((L + 2 * δ)/D) * dM := by
        have h₁ :=
        calc L + C = (L/D) * (D + (D/L) * C) := by field_simp; ring
          _ ≤ (L/D) * (D + 4 * C) := by
              gcongr
              rw [div_le_iff]
              · dsimp [D, L]
                linarith only [hδ₀]
              positivity
          _ ≤ (L/D) * dM := by gcongr
        have h₂ :=
        calc 2 * δ = (2 * δ) / D * D := by field_simp
          _ ≤ (2 * δ)/D * dM := by
              gcongr
              linarith only [I₁, hC]
        rw [add_div, add_mul]
        linarith only [h₁, h₂]
      have aux3 : (1-α) * D + α * 2^k * dM ≤ dM * 2^k - C/2 - QC k := by
        dsimp [QC]
        split_ifs with h
        · simp only [h, pow_zero]
          dsimp [α, D] at I₁ ⊢
          linarith only [I₁, hδ₀, hC]
        have :=
        calc C/2 + 8 * δ + (1-α) * D
            ≤ 2 * (1-α) * dM := by
              dsimp [α, D] at I₁ ⊢
              linarith only [I₁, hδ₀, hC]
          _ = 2 ^ 1 * (1-α) * dM := by ring
          _ ≤ 2^k * (1-α) * dM := by
              gcongr
              · norm_num
              · show 0 < k
                positivity
        linarith only [this]

      have proj_mem {r : ℝ} (hr : r ∈ Icc x uM) : q k r ∈ projSet (f r) (V k) := by
        dsimp [q, V]
        convert [p r‒f r].projSet_thickening' (E := dist (p r) (f r)) (hp _) ?_ ?_ (by rfl) using 2
        · rw [[p r‒f r].param2]
        · positivity
        · rw [dist_comm]
          exact le_trans H₁ (hx₂ _ hr)

      have h_x_uM_subset : Icc x uM ⊆ Icc um uM := by
        rw [Icc_subset_Icc_iff] at h_yM_uM_subset ⊢
        · exact ⟨h_yM_uM_subset.1.trans hx₁.1, h_yM_uM_subset.2⟩
        · exact hx₁.2
        · exact hyM.2
      /- Construct a point `w` such that its projection on `V k` is close to that of `uM`
      and therefore far away from that of `x`. This is just the intermediate value theorem
      (with some care as the closest point projection is not continuous). -/
      obtain ⟨w, hw₁, hw₂, hw₃⟩ : ∃ w ∈ Icc x uM,
          dist (q k uM) (q k w) ∈ Icc ((9 * δ + 4 * QC k) - 4 * δ - 2 * QC k) (9 * δ + 4 * QC k)
          ∧ (∀ v ∈ Icc w uM, dist (q k uM) (q k v) ≤ 9 * δ + 4 * QC k) := by
        apply quasi_convex_projection_small_gaps' (f := f) (G := V k)
        · exact hf.mono h_x_uM_subset
        · exact hx₁.2
        · exact V_quasiconvex _
        · intro w hw
          apply proj_mem hw
        · exact hδ
        · have := QC_nonneg k
          rw [dist_comm]
          refine ⟨?_, le_trans ?_ hx₃⟩
          · ring_nf
            linarith only [this, hδ₀]
          · dsimp [L]
            ring_nf
            linarith only [this, hδ₀]

      /- There are now two cases to be considered: either one can find a point `v` between
      `w` and `uM` which is close enough to `H`. Then this point will satisfy~\eqref{eq:xvK},
      and we will be able to prove the desired inequality. Or there is no such point,
      and then `w` will have the good properties at step `k+1` -/
      by_cases h : ∃ v ∈ Icc w uM, dist (f v) (p v) ≤ (2^(k+2)-1) * dM
      /- First subcase: there is a good point `v` between `w` and `uM`. This is the
      heart of the argument: we will show that the desired inequality holds. -/
      · left
        obtain ⟨v, hv₁, hv₂⟩ := h

        -- Auxiliary basic fact to be used later on.
        have aux4 {r : ℝ} (hr : r ∈ Icc x v) : dM * 2 ^ k ≤ infDist (f r) (V k) := by
          have hr : r ∈ Icc x uM := ⟨hr.1, hr.2.trans hv₁.2⟩
          have h₁ :=
          calc infDist (f r) (V k)
              = dist ({p r‒f r}.param (p r) (dist (p r) (f r)))
                  ({p r‒f r}.param (p r) ((2 ^ k - 1) * dM)) := by
                  rw [← (proj_mem hr).2]
                  dsimp [q]
                  rw [[p r‒f r].param2]
              _ = |dist (p r) (f r) - (2 ^ k - 1) * dM| := by
                  apply [p r‒f r].param7
                  · simpa using dist_nonneg
                  refine ⟨by positivity, ?_⟩
                  rw [dist_comm]
                  exact le_trans H₁ (hx₂ _ hr)
              _ = dist (f r) (p r) - (2 ^ k - 1) * dM := by
                  rw [dist_comm (p r), abs_of_nonneg]
                  linarith only [hx₂ r hr, H₁]
          have h₂ : (2^(k+1) - 1) * dM ≤ dist (f r) (p r) := hx₂ _ hr
          ring_nf at h₂
          linarith only [h₁, h₂]

        /- Substep 1: We can control the distance from `f v` to `f closestm` in terms of the distance
        of the distance of `f v` to `H`, i.e., by `2^k * dM`. The same control follows
        for `v - closestm` thanks to the quasi-isometry property. Then, we massage this
        inequality to put it in the form we will need, as an upper bound on `(x-v) * exp (-2^k * dM)`. -/
        have :=
        calc |closestm - v| ≤ Λ * (infDist (f closestm) H + (L + C + 2 * δ) + infDist (f v) H) := by
              apply hD hclosestm.1 ⟨?_, hv₁.2⟩
              linarith only [hv₁.1, hw₁.1, hx₁.1]
          _ ≤ Λ * (dm + (L + C + 2 * δ) + (2^(k+2)-1) * dM) := by
              gcongr
              rw [← (hp v).2]
              exact hv₂
          _ = Λ * (dm + 1 * (L + C + 2 * δ) + (2^(k+2)-1) * dM) := by ring
          _ ≤ Λ * (dM + 2^k * (((L + 2 * δ)/D) * dM) + (2^(k+2)-1) * dM) := by
              gcongr
          _ = Λ * 2^k * (4 + (L + 2 * δ)/D) * dM := by ring
        have : |v - closestm| / (Λ * (4 + (L + 2 * δ)/D)) ≤ 2^k * dM := by
          rw [div_le_iff]
          convert this using 1
          · rw [abs_sub_comm]
          · ring
          · positivity
        /- We reformulate this control inside of an exponential, as this is the form we
        will use later on. -/
        have :=
        calc exp (- (α * (2^k * dM) * log 2 / (5 * δ)))
            ≤ exp (-(α * (|v - closestm| / (Λ * (4 + (L + 2 * δ)/D))) * log 2 / (5 * δ))) := by
              gcongr
          _ = exp (-K * |v - closestm|) := by
              dsimp [K]
              congr
              field_simp
              ring
          _ = exp (-K * (v - closestm)) := by
              congr
              rw [abs_of_nonneg]
              linarith only [hv₁.1, hw₁.1, hx₁.1, hyM.1, hym.2, hclosestm.1.2]
        have : 0 ≤ v - x := by linarith only [hv₁.1, hw₁.1]
        -- Plug in `v-x` to get the final form of this inequality.
        have :=
        calc K * (v - x) * exp (- (α * (2^k * dM) * log 2 / (5 * δ)))
            ≤ K * (v - x) * exp (-K * (v - closestm)) := by gcongr
          _ = ((K * (v - x) + 1) - 1) * exp (- K * (v - closestm)) := by ring
          _ ≤ (exp (K * (v - x)) - 1) * exp (-K * (v - closestm)) := by gcongr; apply add_one_le_exp
          _ = exp (-K * (x - closestm)) - exp (-K * (v - closestm)) := by
              rw [sub_mul, ← exp_add]
              ring_nf
          _ ≤ exp (-K * (x - closestm)) - exp (-K * (uM - um)) := by
              gcongr _ - exp ?_
              apply mul_le_mul_of_nonpos_left
              · linarith only [hv₁.2, hclosestm.1.1]
              rw [Left.neg_nonpos_iff]
              positivity
        have B : (v - x) * exp (- (α * (2^k * dM) * log 2 / (5 * δ)))
            ≤ (exp (-K * (x - closestm)) - exp (-K * (uM-um)))/K := by
          rw [le_div_iff]
          · convert this using 1
            ring
          positivity
        -- End of substep 1

        /- Substep 2: The projections of `f v` and `f x` on the cylinder `V k` are well separated,
        by construction. This implies that `v` and `x` themselves are well separated, thanks
        to the exponential contraction property of the projection on the quasi-convex set `V k`.
        This leads to a uniform lower bound for `(x-v) * exp (-2^k * dM)`, which has been upper bounded
        in Substep 1. -/
        have :=
        calc L - 4 * δ + 7 * QC k ≤ dist (q k uM) (q k x) := hx₃
          _ ≤ dist (q k uM) (q k v) + dist (q k v) (q k x) := dist_triangle ..
          _ ≤ (9 * δ + 4 * QC k) + dist (q k v) (q k x) := by
              gcongr
              apply hw₃ _ hv₁
        have :=
        calc L - 13 * δ + 3 * QC k ≤ dist (q k v) (q k x) := by linarith only [this]
          _ ≤ 3 * QC k + max (5 * deltaG X)
                ((4 * exp (1/2 * log 2)) * Λ * (v - x)
                * exp (-(dM * 2^k - C/2 - QC k) * log 2 / (5 * δ))) := by
              /- We use different statements for the projection in the case `k = 0` (projection on
              a geodesic) and `k > 0` (projection on a quasi-convex set) as the bounds are better in
              the first case, which is the most important one for the final value of the constant. -/
              obtain rfl | hk := eq_or_ne k 0
              · have : dist (q 0 x) (q 0 v)
                    ≤ max (5 * deltaG X)
                      ((4 * exp (1/2 * log 2)) * Λ * (v - x)
                      * exp (-(dM * 2^0 - C/2) * log 2 / (5 * δ))) := by
                  apply geodesic_projection_exp_contracting (G := V 0) (f := f)
                  · intro x1 x2 hx1 hx2
                    apply hf'.upper_bound
                    · exact ⟨by linarith only [hx1.1, hx₁.1, hyM.1, hz.1],
                        by linarith only [hv₁.2, hx1.2]⟩
                    · exact ⟨by linarith only [hx2.1, hx₁.1, hyM.1, hz.1],
                        by linarith only [hv₁.2, hx2.2]⟩
                  · exact hw₁.1.trans hv₁.1
                  · simpa [hq0, V, H_closure] using hp x
                  · simpa [hq0, V, H_closure] using hp v
                  · intro t
                    exact aux4
                  · simp only [pow_zero]
                    dsimp [D] at I₁
                    linarith only [I₁, hC, hδ₀]
                  · exact hδ
                  · exact hC
                  · positivity
                  · simpa [V, H_closure] using h_H''
                simpa [hq0, QC, dist_comm] using this
              · have : dist (q k x) (q k v)
                    ≤ 2 * QC k + 8 * δ + max (5 * deltaG X)
                      ((4 * exp (1/2 * log 2)) * Λ * (v - x) * exp (-(dM * 2^k - QC k -C/2) * log 2 / (5 * δ))) := by
                  apply quasiconvex_projection_exp_contracting (G := V k) (f := f)
                  · intro x1 x2 hx1 hx2
                    apply hf'.upper_bound
                    · exact ⟨by linarith only [hx1.1, hx₁.1, hyM.1, hz.1],
                        by linarith only [hv₁.2, hx1.2]⟩
                    · exact ⟨by linarith only [hx2.1, hx₁.1, hyM.1, hz.1],
                        by linarith only [hv₁.2, hx2.2]⟩
                  · exact hw₁.1.trans hv₁.1
                  · apply proj_mem
                    exact ⟨by rfl, hx₁.2⟩
                  · apply proj_mem
                    exact ⟨hw₁.1.trans hv₁.1, hv₁.2⟩
                  · intro t
                    exact aux4
                  · dsimp [QC]
                    rw [if_neg hk]
                    dsimp [D] at I₁
                    linarith only [hδ₀, hC, I₁, aux.2.2]
                  · exact hδ
                  · exact hC
                  · positivity
                  · apply V_quasiconvex
                rw [dist_comm]
                refine le_trans this ?_
                simp only [if_neg hk, QC]
                ring_nf
                rfl

        have : L - 13 * δ ≤ max (5 * deltaG X)
          ((4 * exp (1/2 * log 2)) * Λ * (v - x) * exp (-(dM * 2^k - C/2 - QC k) * log 2 / (5 * δ))) := by
          linarith only [this]
        have A :=
        calc L - 13 * δ
            ≤ (4 * exp (1/2 * log 2)) * Λ * (v - x)
              * exp (-(dM * 2^k - C/2 - QC k) * log 2 / (5 * δ)) := by
              rw [le_max_iff] at this
              apply this.resolve_left
              push_neg
              dsimp [L]
              linarith only [hδ]
          /- We separate the exponential gain coming from the contraction into two parts, one
          to be spent to improve the constant, and one for the inductive argument. -/
          _ ≤ (4 * exp (1/2 * log 2)) * Λ * (v - x)
              * exp (-((1-α) * D + α * 2^k * dM) * log 2 / (5 * δ)) := by
              gcongr -- `aux3`
          _ = (4 * exp (1/2 * log 2)) * Λ * 1 * ((v - x)
              * (exp (-(1-α) * D * log 2 / (5 * δ)) * exp (-α * 2^k * dM * log 2 / (5 * δ)))) := by
              rw [← exp_add]
              ring_nf
          _ = (4 * exp (1/2 * log 2)) * Λ * exp (-((1-α) * D * log 2 / (5 * δ))) * ((v - x)
              * exp (-(α * (2^k * dM) * log 2 / (5 * δ)))) := by
              ring_nf
        -- This is the end of the second substep.

        /- Use the second substep to show that `x-v` is bounded below, and therefore
        that `closestM - x` (the endpoints of the new geodesic we want to consider in the
        inductive argument) are quantitatively closer than `uM - um`, which means that we
        will be able to use the inductive assumption over this new geodesic. -/
        have :=
        calc L - 13 * δ
            ≤ (4 * exp (1/2 * log 2)) * Λ * exp (-((1-α) * D * log 2 / (5 * δ))) * ((v - x) * exp (-(α * (2^k * dM) * log 2 / (5 * δ)))) := A  --
          _ ≤ (4 * exp (1/2 * log 2)) * Λ * exp 0 * ((v - x) * exp 0) := by
              gcongr
              · rw [Left.neg_nonpos_iff]
                positivity
              · rw [Left.neg_nonpos_iff]
                positivity
          _ = (4 * exp (1/2 * log 2)) * Λ * (v-x) := by simp
          _ ≤ 20 * Λ * (v - x) := by
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
        have : (1/4) * δ / Λ ≤ v - x := by
          rw [div_le_iff]
          · dsimp [L] at this
            linarith only [this]
          positivity
        have :=
        calc (1/4) * δ / Λ
            ≤ v - x := by linarith only [this]
          _ ≤ uM - um - x + closestm := by linarith only [hclosestm.1.1, hv₁.2]

        -- start to set up for the well-founded induction
        have h₂ : z ∈ Icc closestm x :=
          ⟨by linarith only [hym.2, hclosestm.1.2], by linarith only [hx₁.1, hyM.1]⟩
        have h₁ : closestm ≤ x := h₂.1.trans h₂.2
        have : Nat.floor (4 * Λ * |x - closestm| / δ) < Nat.floor (4 * Λ * |uM - um| / δ) := by
          calc Nat.floor (4 * Λ * |x - closestm| / δ) < Nat.floor (4 * Λ * |x - closestm| / δ + 1) := by
                rw [Nat.floor_add_one]
                · omega
                positivity
            _ ≤ Nat.floor (4 * Λ * |uM - um| / δ) := by
                gcongr
                rw [le_div_iff]
                rw [div_le_iff] at this
                field_simp
                rw [abs_of_nonneg, abs_of_nonneg]
                linarith only [this]
                · positivity
                · linarith only [h₁]
                all_goals positivity

        /- Conclusion of the proof: combine the lower bound of the second substep with
        the upper bound of the first substep to get a definite gain when one goes from
        the old geodesic to the new one. Then, apply the inductive assumption to the new one
        to conclude the desired inequality for the old one. -/
        have : 0 < (L - 13 * δ) := by
          dsimp [L]
          ring_nf
          positivity
        have H₂ :=
        calc L + 4 * δ = ((L + 4 * δ)/(L - 13 * δ)) * (L - 13 * δ) := by field_simp
          _ ≤ ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp (1/2 * log 2)) * Λ
              * exp (- ((1 - α) * D * log 2 / (5 * δ))) * ((v - x)
              * exp (- (α * (2 ^ k * dM) * log 2 / (5 * δ))))) := by gcongr
          _ ≤ ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp (1/2 * log 2)) * Λ
              * exp (- ((1 - α) * D * log 2 / (5 * δ)))
              * ((exp (-K * (x - closestm)) - exp (-K * (uM - um)))/K)) := by gcongr
          _ = Kmult * (exp (-K * (x - closestm)) - exp (-K * (uM - um))) := by
              dsimp [Kmult]
              ring

        calc gromovProductAt (f z) (f um) (f uM)
            ≤ gromovProductAt (f z) (f closestm) (f x) + (L + 4 * δ) := Rec hclosestm.1 hx₁
          _ ≤ (Λ ^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ
              + Kmult * (1 - exp (- K * (x - closestm))))
              + (Kmult * (exp (-K * (x - closestm)) - exp (-K * (uM-um)))) := by
              have h₃ : Icc closestm x ⊆ Icc um uM := by
                rw [Icc_subset_Icc_iff h₁]
                exact ⟨hclosestm.1.1, hx₁.2⟩
              have := Morse_Gromov_theorem_aux0 (hf.mono h₃) (hf'.mono h₃) h₁ h₂ hδ
              dsimp [D, K, Kmult, L] at this H₂ ⊢
              linarith only [this, H₂]
          _ = (Λ^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (uM - um)))) := by
              dsimp [K]
              ring
        -- End of the first subcase, when there is a good point `v` between `w` and `uM`.

      /- Second subcase: between `w` and `uM`, all points are far away from `V k`. We
      will show that this implies that `w` is admissible for the step `k+1`. -/
      · right
        push_neg at h
        refine ⟨w, ⟨hx₁.1.trans hw₁.1, hw₁.2⟩, fun x hx ↦ (h x hx).le, ?_⟩
        have h₁ : dist (q k uM) (q (k+1) uM) = 2^k * dM := by
          dsimp [q]
          rw [[p uM‒f uM].param7]
          · rw [abs_of_nonpos]
            · ring
            · ring_nf
              linarith only [hdM_mul]
          · refine ⟨by positivity, ?_⟩
            rw [dist_comm]
            exact H₁.trans (hx₂ _ ⟨hx₁.2, by rfl⟩)
          · refine ⟨by positivity, ?_⟩
            rw [dist_comm]
            refine le_trans ?_ (hx₂ _ ⟨hx₁.2, by rfl⟩)
            ring_nf
            linarith only [hdM_mul]
        have h₂ : dist (q k w) (q (k+1) w) = 2^k * dM := by
          dsimp [q]
          rw [[p w‒f w].param7]
          · rw [abs_of_nonpos]
            · ring
            · ring_nf
              linarith only [hdM_mul]
          · refine ⟨by positivity, ?_⟩
            rw [dist_comm]
            exact H₁.trans (hx₂ _ hw₁)
          · refine ⟨by positivity, ?_⟩
            rw [dist_comm]
            refine le_trans ?_ (hx₂ _ hw₁)
            ring_nf
            linarith only [hdM_mul]
        have i : q k uM ∈ projSet (q (k+1) uM) (V k) := by
          refine [p uM‒f uM].projSet_thickening' (hp _) ?_ H₁ ?_
          · positivity
          · rw [dist_comm]
            refine le_trans ?_ (h _ ⟨hw₁.2, by rfl⟩).le
            rw [← sub_nonneg]
            ring_nf
            positivity
        have j : q k w ∈ projSet (q (k+1) w) (V k) := by
          refine [p w‒f w].projSet_thickening' (hp _) ?_ H₁ ?_
          · positivity
          · rw [dist_comm]
            refine le_trans ?_ (h _ ⟨by rfl, hw₁.2⟩).le
            rw [← sub_nonneg]
            ring_nf
            positivity
        have : 5 * δ + 2 * QC k ≤ dist (q (k + 1) uM) (q (k + 1) w) - dist (q k uM) (q (k + 1) uM)
                    - dist (q k w) (q (k + 1) w) + 10 * δ + 4 * QC k := by
          have := proj_along_quasiconvex_contraction (V_quasiconvex k) i j
          rw [le_max_iff] at this
          obtain h₁ | h₂ := this
          · linarith only [h₁, hw₂.1, hδ]
          · linarith only [h₂, hw₂.1, hδ]
        calc L - 4 * δ + 7 * QC (k+1) ≤ 2 * dM - 5 * δ - 2 * QC k := by
              have h₁ : QC (k + 1) = 8 * δ := by simp [QC]
              have h₂ : QC k ≤ 8 * δ := by
                dsimp only [QC]
                split_ifs
                · positivity
                · rfl
              dsimp [L]
              dsimp [D] at I₁
              linarith only [I₁, h₁, h₂, hC, hδ₀]
          _ ≤ 2^(k+1) * dM - 5 * δ - 2 * QC k := by
              gcongr
              ring_nf
              linarith only [h_pow]
          _ ≤ dist (q (k + 1) uM) (q (k + 1) w) := by
              ring_nf at this h₁ h₂ ⊢
              linarith only [this, h₁, h₂]

    /- This is the end of the main induction over `k`. To conclude, choose `k` large enough
    so that the second alternative in this induction is impossible. It follows that the first
    alternative holds, i.e., the desired inequality is true. -/
    obtain ⟨k, hk⟩ : ∃ k, 2^k > dist (f uM) (p uM)/dM + 1 := by
      refine tendsto_pow_atTop_atTop_of_one_lt ?_ |>.eventually_gt_atTop _ |>.exists
      norm_num
    apply (Ind_k k).resolve_right
    push_neg
    intro x hx₁ hx₂
    have H₁ :=
    calc dist (f uM) (p uM) = ((dist (f uM) (p uM)/dM + 1) - 1) * dM := by field_simp
      _ < (2^k - 1) * dM := by gcongr
      _ ≤ (2^(k + 1) - 1) * dM := by
          gcongr
          · norm_num
          · linarith only []
    have H₂ := hx₂ uM ⟨hx₁.2, by rfl⟩
    linarith only [H₁, H₂]
    -- end of the case where `D + 4 * C ≤ dM` and `dm ≤ dM`.
termination_by Nat.floor (4 * Λ * |uM - um| / δ)
