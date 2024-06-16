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

variable {δ : ℝ}

/- We give their values to the parameters `L`, `D` and `α` that we will use in the proof. -/
local notation "α" => 12 / 100
local notation "L" => 18 * δ
local notation "D" => 55 * δ

open GromovHyperbolicSpace

/-- Let `f` be a continuous quasi-geodesic on the interval $[u, y]$, and let `H` be a geodesic.
Given that `f` is everywhere at least a certain distance from `H`, and given that the projections
of the endpoints onto `H` are at least a certain distance apart, there exists `v` in $[u, y]$
such that `y - v` is bounded below by a quantity which is exponential in `v`'s
distance from `H`. -/
theorem Morse_Gromov_theorem_aux_m {f : ℝ → X}
    {u y : ℝ} (hf : ContinuousOn f (Icc u y)) {Λ C : ℝ} (hC : 0 ≤ C) (hΛ : 0 ≤ Λ)
    (hf' : ∀ s t, s ∈ Icc u y → t ∈ Icc u y → dist (f s) (f t) ≤ Λ * |s - t| + C)
    (h_u_y : u ≤ y)
    {H : Set X} (h_H' : GeodesicSegment H)  (hδ : δ > deltaG X) {p : ℝ → X}
    (hp : ∀ t, p t ∈ projSet (f t) H)
    (d : ℝ) (hclosest : ∀ v ∈ Icc u y, d ≤ infDist (f v) H)
    (I₁ : D + 4 * C ≤ d) (I₂ : L - 4 * δ ≤ dist (p u) (p y)) :
    ∃ v ∈ Icc u y,
      L - 13 * δ
        ≤ (4 * exp (1/2 * log 2)) * Λ * exp (-((1-α) * D * log 2 / (5 * δ))) * ((y - v)
          * exp (-(α * max d ((dist (f v) (p v) + d) / 4) * log 2 / (5 * δ)))) := by
  have : Inhabited X := ⟨f u⟩
  have hδ₀ : 0 < δ := by linarith only [hδ, delta_nonneg X]
  have H_closure : closure H = H := by
    obtain ⟨_, _, h_H⟩ := h_H'
    exact h_H.isClosed.closure_eq
  /- Case 2.2: `d` is large, i.e., all points in $f[u, y]$ are far away from `H`. Moreover,
  assume that `d ≥ dM`. Then we will find a pair of points `v` and `x` with `u ≤ v ≤ x ≤ y`
  satisfying the estimate~\eqref{eq:xvK}. We argue by induction: while we
  have not found such a pair, we can find a point `x_k` whose projection on `V_k`, the
  neighborhood of size `(2^k-1) * d` of `H`, is far enough from the projection of `u`, and
  such that all points in between are far enough from `V_k` so that the corresponding
  projection will have good contraction properties. -/
  let QC : ℕ → ℝ := fun k ↦ if k = 0 then 0 else 8 * δ
  have QC_nonneg (k : ℕ) : 0 ≤ QC k := by dsimp [QC]; split <;> positivity

  · have : 0 < d := by linarith only [I₁, hC, hδ₀]
    let V : ℕ → Set X := fun k ↦ cthickening ((2^k - 1) * d) H
    have Q (k : ℕ) : Quasiconvex (0 + 8 * deltaG X) (V k) := by
      apply h_H'.quasiconvex.cthickening
      have : 1 ≤ (2:ℝ) ^ k := one_le_pow_of_one_le (by norm_num) k
      have : 0 ≤ (2:ℝ) ^ k - 1 := by linarith only [this]
      positivity
    have V_quasiconvex (k : ℕ) : Quasiconvex (QC k) (V k) := by
      dsimp [QC]
      split_ifs with h
      · simp only [h, pow_zero, sub_self, zero_mul, V, cthickening_zero]
        rw [H_closure]
        apply h_H'.quasiconvex
      · refine (Q k).mono ?_
        linarith only [hδ]

    -- Define `q k x` to be the projection of `f x` on `V k`.
    let q : ℕ → ℝ → X := fun k x ↦ {p x‒f x}.param (p x) ((2^k - 1) * d)
    have hq0 (x : ℝ) : q 0 x = p x := by
      dsimp [q]
      convert [p x‒f x].param1
      simp

    -- We introduce a certain property of natural numbers `k` which will eventually let us select
    -- our endpoint `x`.
    let P (k : ℕ) := ∃ x ∈ Icc u y, dist (q k u) (q k x) ≥ L - 4 * δ + 7 * QC k
      ∧ ∀ w ∈ Icc u x, dist (f w) (p w) ≥ (2^(k+1)-1) * d

    /- The property holds for `k = 0`, i.e. there is a point far enough from `q 0 u` on `H`. This
    is just the right endpoint `y`, by construction. -/
    have hP₀ : P 0 := by
      refine ⟨y, ?_, ?_, ?_⟩
      · simp [h_u_y]
      · simp only [hq0, QC, reduceIte]
        linarith only [I₂]
      · intro w hw
        change _ ≤ _
        convert hclosest w hw
        · ring
        · rw [(hp w).2]

    /- The property fails for `k` sufficiently large, by considering the left endpoint `u`. -/
    have hP : ∀ᶠ k in atTop, ¬ P k := by
      have H : ∀ᶠ k in atTop, dist (f u) (p u) < (2 ^ (k + 1) + -1) * d := by
        refine tendsto_atTop_add_const_right _ (-1:ℝ)
          (tendsto_pow_atTop_atTop_of_one_lt (r := (2:ℝ)) ?_)
          |>.atTop_mul_const (r := d) ?_
          |>.comp (tendsto_add_atTop_nat 1)
          |>.eventually_gt_atTop _
        · norm_num
        · positivity
      filter_upwards [H] with k hk
      dsimp [P]
      push_neg
      intro t ht _
      exact ⟨u, ⟨by rfl, ht.1⟩, hk⟩

    -- Thus there exists a natural number `k` such that `P k` holds and `P (k + 1)` doesn't.
    -- Select the witness `x` for this `k`.
    obtain ⟨k, hk₁, hk₂⟩ : ∃ k, P k ∧ ¬ P (k + 1) := by -- there should be a lemma for this!
      by_contra! h
      obtain ⟨k, hk⟩ := hP.exists
      exact hk (Nat.rec hP₀ h k)
    obtain ⟨x, hx₁, hx₃, hx₂⟩ :
      ∃ x ∈ Icc u y, L - 4 * δ + 7 * QC k ≤ dist (q k u) (q k x)
        ∧ (∀ w, w ∈ Icc u x → dist (f w) (p w) ≥ (2^(k+1)-1) * d) := hk₁

    -- FIXME these are basically `aux`, deduplicate
    have h_pow : (1:ℝ) ≤ 2 ^ k := one_le_pow_of_one_le (by norm_num) k
    have h_pow' : 0 ≤ (2:ℝ) ^ k - 1 := by linarith only [h_pow]
    have h_pow'' : (1:ℝ) ≤ 2 ^ (k + 1) := one_le_pow_of_one_le (by norm_num) _
    have h_pow''' : 0 ≤ (2:ℝ) ^ (k + 1) - 1 := by linarith only [h_pow'']
    have hd_mul : 0 ≤ d * 2 ^ k := by positivity
    have H₁ : (2 ^ k - 1) * d ≤ (2 ^ (k + 1) - 1) * d := by ring_nf; linarith only [hd_mul]

    -- Some auxiliary technical inequalities to be used later on.
    have aux : (2 ^ k - 1) * d ≤ (2*2^k-1) * d ∧ 0 ≤ 2 * 2 ^ k - (1:ℝ) ∧ d ≤ d * 2 ^ k := by
      refine ⟨?_, ?_, ?_⟩
      · convert H₁ using 1
        ring
      · convert h_pow''' using 1
        ring
      · calc _ = d * 1 := by ring
          _ ≤ _ := by gcongr
    have aux3 : (1-α) * D + α * 2^k * d ≤ d * 2^k - C/2 - QC k := by
      dsimp [QC]
      split_ifs with h
      · simp only [h, pow_zero]
        linarith only [I₁, hδ₀, hC]
      have :=
      calc C/2 + 8 * δ + (1-α) * D
          ≤ 2 * (1-α) * d := by linarith only [I₁, hδ₀, hC]
        _ = 2 ^ 1 * (1-α) * d := by ring
        _ ≤ 2^k * (1-α) * d := by
            gcongr
            · norm_num
            · show 0 < k
              positivity
      linarith only [this]

    have proj_mem {r : ℝ} (hr : r ∈ Icc u x) : q k r ∈ projSet (f r) (V k) := by
      dsimp [q, V]
      convert [p r‒f r].projSet_thickening' (E := dist (p r) (f r)) (hp _) ?_ ?_ (by rfl) using 2
      · rw [[p r‒f r].param2]
      · positivity
      · rw [dist_comm]
        exact le_trans H₁ (hx₂ _ hr)

    have h_u_x_subset : Icc u x ⊆ Icc u y := Icc_subset_Icc (le_refl _) hx₁.2
    /- Construct a point `w` such that its projection on `V k` is O(δ)-close to that of `u`
    and therefore far away from that of `x`. This is just the intermediate value theorem
    (with some care as the closest point projection is not continuous). -/
    obtain ⟨w, hw₁, hw₂, hw₃⟩ : ∃ w ∈ Icc u x,
        dist (q k u) (q k w) ∈ Icc ((9 * δ + 4 * QC k) - 4 * δ - 2 * QC k) (9 * δ + 4 * QC k)
        ∧ (∀ v ∈ Icc u w, dist (q k u) (q k v) ≤ 9 * δ + 4 * QC k) := by
      apply quasi_convex_projection_small_gaps (f := f) (G := V k)
      · exact hf.mono h_u_x_subset
      · exact hx₁.1
      · exact V_quasiconvex _
      · intro w hw
        apply proj_mem hw
      · exact hδ
      · have := QC_nonneg k
        refine ⟨?_, le_trans ?_ hx₃⟩
        · ring_nf
          linarith only [this, hδ₀]
        · ring_nf
          linarith only [this, hδ₀]

    /- The projections of `u` and `w` onto `V (k + 1)` are necessarily at least O(δ) apart. -/
    have : dist (q (k + 1) u) (q (k + 1) w) ≥ L - 4 * δ + 7 * QC (k + 1) := by
      have h₁ : dist (q k u) (q (k+1) u) = 2^k * d := by
        dsimp [q]
        rw [[p u‒f u].param7]
        · rw [abs_of_nonpos]
          · ring
          · ring_nf
            linarith only [hd_mul]
        · refine ⟨by positivity, ?_⟩
          rw [dist_comm]
          exact H₁.trans (hx₂ _ ⟨by rfl, hx₁.1⟩)
        · refine ⟨by positivity, ?_⟩
          rw [dist_comm]
          refine le_trans ?_ (hx₂ _ ⟨by rfl, hx₁.1⟩)
          ring_nf
          linarith only [hd_mul]
      have h₂ : dist (q k w) (q (k+1) w) = 2^k * d := by
        dsimp [q]
        rw [[p w‒f w].param7]
        · rw [abs_of_nonpos]
          · ring
          · ring_nf
            linarith only [hd_mul]
        · refine ⟨by positivity, ?_⟩
          rw [dist_comm]
          exact H₁.trans (hx₂ _ hw₁)
        · refine ⟨by positivity, ?_⟩
          rw [dist_comm]
          refine le_trans ?_ (hx₂ _ hw₁)
          ring_nf
          linarith only [hd_mul]
      have i : q k u ∈ projSet (q (k+1) u) (V k) := by
        refine [p u‒f u].projSet_thickening' (hp _) ?_ H₁ ?_
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
      have : 5 * δ + 2 * QC k ≤ dist (q (k + 1) u) (q (k + 1) w) - dist (q k u) (q (k + 1) u)
                  - dist (q k w) (q (k + 1) w) + 10 * δ + 4 * QC k := by
        have := proj_along_quasiconvex_contraction (V_quasiconvex k) i j
        rw [le_max_iff] at this
        obtain h₁ | h₂ := this
        · linarith only [h₁, hw₂.1, hδ]
        · linarith only [h₂, hw₂.1, hδ]
      calc L - 4 * δ + 7 * QC (k+1) ≤ 2 * d - 5 * δ - 2 * QC k := by
            have h₁ : QC (k + 1) = 8 * δ := by simp [QC]
            have h₂ : QC k ≤ 8 * δ := by
              dsimp only [QC]
              split_ifs
              · positivity
              · rfl
            linarith only [I₁, h₁, h₂, hC, hδ₀]
        _ ≤ 2^(k+1) * d - 5 * δ - 2 * QC k := by
            gcongr
            ring_nf
            linarith only [h_pow]
        _ ≤ dist (q (k + 1) u) (q (k + 1) w) := by
            ring_nf at this h₁ h₂ ⊢
            linarith only [this, h₁, h₂]

    /- So, since `k` is chosen so that `P (k + 1)` is known to be false, this implies there is a
    good point `v` between `u` and `w`. -/
    dsimp [P] at hk₂
    push_neg at hk₂
    obtain ⟨v, hv₁, hv₂⟩ : ∃ v ∈ Icc u w, dist (f v) (p v) < (2^(k+2)-1) * d :=
      hk₂ w ⟨hw₁.1, hw₁.2.trans hx₁.2⟩ this
    have : 0 ≤ y - v := by linarith only [hv₁.2, hw₁.2, hx₁.2]

    -- Auxiliary basic fact to be used later on.
    have aux4 {r : ℝ} (hr : r ∈ Icc v x) : d * 2 ^ k ≤ infDist (f r) (V k) := by
      have hr : r ∈ Icc u x := ⟨hv₁.1.trans hr.1, hr.2⟩
      have h₁ :=
      calc infDist (f r) (V k)
          = dist ({p r‒f r}.param (p r) (dist (p r) (f r)))
              ({p r‒f r}.param (p r) ((2 ^ k - 1) * d)) := by
              rw [← (proj_mem hr).2]
              dsimp [q]
              rw [[p r‒f r].param2]
          _ = |dist (p r) (f r) - (2 ^ k - 1) * d| := by
              apply [p r‒f r].param7
              · simpa using dist_nonneg
              refine ⟨by positivity, ?_⟩
              rw [dist_comm]
              exact le_trans H₁ (hx₂ _ hr)
          _ = dist (f r) (p r) - (2 ^ k - 1) * d := by
              rw [dist_comm (p r), abs_of_nonneg]
              linarith only [hx₂ r hr, H₁]
      have h₂ : (2^(k+1) - 1) * d ≤ dist (f r) (p r) := hx₂ _ hr
      ring_nf at h₂
      linarith only [h₁, h₂]

    refine ⟨v, ⟨hv₁.1, (hv₁.2.trans hw₁.2).trans hx₁.2⟩, ?_⟩

    /- Substep 2: The projections of `f v` and `f x` on the cylinder `V k` are well separated,
    by construction. This implies that `v` and `x` themselves are well separated, thanks
    to the exponential contraction property of the projection on the quasi-convex set `V k`.
    This leads to a uniform lower bound for `(x-v) * exp (-2^k * d)`, which has been upper bounded
    in Substep 1. -/
    have :=
    calc L - 4 * δ + 7 * QC k ≤ dist (q k u) (q k x) := hx₃
      _ ≤ dist (q k u) (q k v) + dist (q k v) (q k x) := dist_triangle ..
      _ ≤ (9 * δ + 4 * QC k) + dist (q k v) (q k x) := by
          gcongr
          apply hw₃ _ hv₁
    have :=
    calc L - 13 * δ + 3 * QC k ≤ dist (q k v) (q k x) := by linarith only [this]
      _ ≤ 3 * QC k + max (5 * deltaG X)
            ((4 * exp (1/2 * log 2)) * Λ * (x - v) -- FIXME change to `y - v`
            * exp (-(d * 2^k - C/2 - QC k) * log 2 / (5 * δ))) := by
          /- We use different statements for the projection in the case `k = 0` (projection on
          a geodesic) and `k > 0` (projection on a quasi-convex set) as the bounds are better in
          the first case, which is the most important one for the final value of the constant. -/
          obtain rfl | hk := eq_or_ne k 0
          · have : dist (q 0 v) (q 0 x)
                ≤ max (5 * deltaG X)
                  ((4 * exp (1/2 * log 2)) * Λ * (x - v)
                  * exp (-(d * 2^0 - C/2) * log 2 / (5 * δ))) := by
              apply geodesic_projection_exp_contracting (G := V 0) (f := f)
              · intro x1 x2 hx1 hx2
                apply hf'
                · exact ⟨by linarith only [hv₁.1, hx1.1],
                    by linarith only [hx1.2, hx₁.2]⟩
                · exact ⟨by linarith only [hv₁.1, hx2.1],
                    by linarith only [hx2.2, hx₁.2]⟩
              · exact hv₁.2.trans hw₁.2
              · simpa [hq0, V, H_closure] using hp v
              · simpa [hq0, V, H_closure] using hp x
              · intro t
                exact aux4
              · simp only [pow_zero]
                linarith only [I₁, hC, hδ₀]
              · exact hδ
              · exact hC
              · positivity
              · simpa [V, H_closure] using h_H'
            simpa [hq0, QC] using this
          · have : dist (q k v) (q k x)
                ≤ 2 * QC k + 8 * δ + max (5 * deltaG X)
                  ((4 * exp (1/2 * log 2)) * Λ * (x - v) * exp (-(d * 2^k - QC k -C/2) * log 2 / (5 * δ))) := by
              apply quasiconvex_projection_exp_contracting (G := V k) (f := f)
              · intro x1 x2 hx1 hx2
                apply hf'
                · exact ⟨by linarith only [hv₁.1, hx1.1],
                    by linarith only [hx1.2, hx₁.2]⟩
                · exact ⟨by linarith only [hv₁.1, hx2.1],
                    by linarith only [hx2.2, hx₁.2]⟩
              · exact hv₁.2.trans hw₁.2
              · apply proj_mem
                exact ⟨hv₁.1, hv₁.2.trans hw₁.2⟩
              · apply proj_mem
                exact ⟨hx₁.1, by rfl⟩
              · intro t
                exact aux4
              · dsimp [QC]
                rw [if_neg hk]
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
      ((4 * exp (1/2 * log 2)) * Λ * (x - v) * exp (-(d * 2^k - C/2 - QC k) * log 2 / (5 * δ))) := by
      linarith only [this]
    calc L - 13 * δ
        ≤ (4 * exp (1/2 * log 2)) * Λ * (x - v)
          * exp (-(d * 2^k - C/2 - QC k) * log 2 / (5 * δ)) := by
          rw [le_max_iff] at this
          apply this.resolve_left
          push_neg
          linarith only [hδ]
      /- We separate the exponential gain coming from the contraction into two parts, one
      to be spent to improve the constant, and one for the inductive argument. -/
      _ ≤ (4 * exp (1/2 * log 2)) * Λ * (x - v)
          * exp (-((1-α) * D + α * 2^k * d) * log 2 / (5 * δ)) := by
          have : 0 ≤ x - v := by linarith only [hv₁.2, hw₁.2]
          gcongr -- `aux3`
      _ ≤ (4 * exp (1/2 * log 2)) * Λ * (y - v)
          * exp (-((1-α) * D + α * 2^k * d) * log 2 / (5 * δ)) := by
          gcongr
          exact hx₁.2
      _ = (4 * exp (1/2 * log 2)) * Λ * 1 * ((y - v)
          * (exp (-(1-α) * D * log 2 / (5 * δ)) * exp (-α * 2^k * d * log 2 / (5 * δ)))) := by
          rw [← exp_add]
          ring_nf
      _ = (4 * exp (1/2 * log 2)) * Λ * exp (-((1-α) * D * log 2 / (5 * δ))) * ((y - v)
          * exp (-(α * (2^k * d) * log 2 / (5 * δ)))) := by
          ring_nf
      _ ≤ (4 * exp (1/2 * log 2)) * Λ * exp (-((1-α) * D * log 2 / (5 * δ))) * ((y - v)
          * exp (-(α * max d ((dist (f v) (p v) + d) / 4) * log 2 / (5 * δ)))) := by
          gcongr
          apply max_le
          · calc _ = 1 * d := by ring
              _ ≤ 2 ^ k * d := by gcongr
          · ring_nf at hv₂
            linarith only [hv₂]
    -- This is the end of the second substep.

theorem Morse_Gromov_theorem_aux_M {f : ℝ → X}
    {u y : ℝ} (hf : ContinuousOn f (Icc y u)) {Λ C : ℝ} (hC : 0 ≤ C) (hΛ : 0 ≤ Λ)
    (hf' : ∀ s t, s ∈ Icc y u → t ∈ Icc y u → dist (f s) (f t) ≤ Λ * |s - t| + C)
    (h_y_u : y ≤ u)
    {H : Set X} (h_H' : GeodesicSegment H) (hδ : δ > deltaG X) {p : ℝ → X}
    (hp : ∀ t, p t ∈ projSet (f t) H)
    (d : ℝ) (hclosest : ∀ v ∈ Icc y u, d ≤ infDist (f v) H)
    (I₁ : D + 4 * C ≤ d) (I₂ : L - 4 * δ ≤ dist (p u) (p y)) :
    ∃ v ∈ Icc y u,
      L - 13 * δ
        ≤ (4 * exp (1/2 * log 2)) * Λ * exp (-((1-α) * D * log 2 / (5 * δ))) * ((v - y)
          * exp (-(α * max d ((dist (f v) (p v) + d) / 4) * log 2 / (5 * δ)))) := by
  have key := Morse_Gromov_theorem_aux_m (Λ := Λ) (C := C) (f := f ∘ Neg.neg) (u := -u)
    (y := - y) (H := H) (d := d) (p := p ∘ Neg.neg) ?_ hC hΛ ?_ ?_ h_H' hδ ?_ ?_
    I₁ ?_
  obtain ⟨v', hv', h₁⟩ := key
  refine ⟨-v', ?_, ?_⟩
  · rw [neg_mem_Icc_iff]
    simpa using hv'
  · convert h₁ using 3
    ring
  · refine hf.comp (s := Icc (-u) (-y)) continuousOn_neg ?_
    intro x hx
    rwa [neg_mem_Icc_iff]
  · intro a b ha hb
    convert hf' (s := -a) (t := -b) ?_ ?_ using 2
    · rw [← abs_neg]
      ring_nf
    · rwa [neg_mem_Icc_iff]
    · rwa [neg_mem_Icc_iff]
  · simpa using h_y_u
  · intro t
    exact hp (-t)
  · intro v hv
    apply hclosest
    rwa [neg_mem_Icc_iff]
  · simpa using I₂

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
    (hδ : δ > deltaG X) :
    /- We define two constants `K` and `Kmult` that appear in the precise formulation of the
    bounds. Their values have no precise meaning, they are just the outcome of the computation. -/
    let K : ℝ := α * log 2 / (5 * (4 + (L + 2 * δ)/D) * δ * Λ)
    let Kmult : ℝ := ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp (1/2 * log 2)) * Λ * exp (- ((1 - α) * D * log 2 / (5 * δ))) / K)
    gromovProductAt (f z) (f um) (f uM)
      ≤ Λ^2 * (D + (3/2) * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (uM - um))) := by
  have hC := hf'.C_nonneg
  have := hf'.one_le_lambda
  have : Inhabited X := ⟨f 0⟩
  have hδ₀ : 0 < δ := by linarith only [hδ, delta_nonneg X]
  intro K Kmult

  have : 0 < K := by ring_nf; positivity
  have : 1 ≤ Λ ^ 2 := by nlinarith only [hf'.one_le_lambda]
  have : Kmult > 0 := by ring_nf; positivity

  have : 0 ≤ uM - um := by linarith only [h_um_uM]
  by_cases hz_um_uM_L : gromovProductAt (f z) (f um) (f uM) ≤ L
  · /- If `f z` is already close to the geodesic, there is nothing to do, and we do not need
    the induction assumption. This is case 1 in the description above. -/
    calc gromovProductAt (f z) (f um) (f uM) ≤ L := hz_um_uM_L
      _ ≤ 1 * (D + (3/2) * L + δ + 11/2 * C) - 2 * δ + 0 * (1 - exp (- K * (uM - um))) := by
        linarith only [hf'.C_nonneg, hδ₀]
      _ ≤ Λ^2 * (D + (3/2) * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (uM - um))) := by
        gcongr
        have : 0 ≤ K * (uM - um) := by positivity
        simpa using this

  /- We come to the interesting case where `f z` is far away from a geodesic between
  `f um` and `f uM`. Let `m` be close to a projection of `f z` on such a geodesic (we use
  the opposite point of `f z` on the corresponding tripod).
  We will push the points `f um` and `f uM` towards `f z` by considering points whose projection on
  a geodesic `H` between `m` and `z` is roughly at distance
  `gromovProductAt (f z) (f um) (f uM) - L` of `f z`. -/
  let m := {(f um)‒(f uM)}.param (f um) (gromovProductAt (f um) (f z) (f uM))

  let H : Set X := {(f z)‒m}
  have h_H : GeodesicSegmentBetween H (f z) m := [(f z)‒m]
  have h_H' : GeodesicSegment H := ⟨_, _, h_H⟩
  have H_closure: closure H = H := by rw [h_H.isClosed.closure_eq]

  -- Introduce the notation `p` for some projection on the geodesic `H`.
  have H_nonempty (r : ℝ) : (projSet (f r) H).Nonempty :=
    projSet_nonempty_of_compact h_H.isCompact h_H.nonempty _
  choose p hp using H_nonempty
  have pH (r : ℝ) : p r ∈ H := (hp r).1
  have pz : p z = f z := by simpa [distproj_self h_H.left_mem] using hp z

  have I : dist (f um) m + dist m (f uM) = dist (f um) (f uM)
            ∧ dist (f um) m = gromovProductAt (f um) (f z) (f uM) := by
    constructor
    · apply [(f um)‒(f uM)].dist_eq
      apply [(f um)‒(f uM)].param3
      simp
    · apply [(f um)‒(f uM)].param6
      simp

  set G := gromovProductAt (f z) (f um) (f uM)
  have h_fz_m_G : dist (f z) m ≤ G + 2 * δ :=
    calc _ ≤ G + 2 * deltaG X := dist_triangle_side_middle _ [(f um)‒(f uM)]
      _ ≤ G + 2 * δ := by rel [hδ]
  clear_value m

  -- The point `p um` lies at nearly at the `m`- end of the geodesic `H` (at least a distance `G`
  -- from `f z`)
  have h_fz_pum_G : G ≤ dist (f z) (p um) := by
    have :=
    calc dist (f um) (f z) ≤ dist (f um) (p um) + dist (p um) (f z) := dist_triangle ..
      _ ≤ dist (f um) m + dist (p um) (f z) := by
        gcongr
        exact projSet_dist_le h_H.right_mem (hp um)
    simp only [G, gromovProductAt, dist_comm] at this I ⊢
    linarith only [this, I.2]

  -- Choose a point `f ym` to the left of `z` whose projection on `H` is roughly at distance `G - L`
  -- of `f z`.
  obtain ⟨ym, hym, hym_dist, hym₂⟩ : ∃ ym ∈ Icc um z,
      L - 4 * δ ≤ dist (p um) (p ym) ∧ ∀ x ∈ Icc um ym, G ≤ dist (f z) (p x) + L := by
    obtain ⟨ym, hym⟩ : ∃ ym ∈ Icc um z,
        (dist (p um) (p ym)
          ∈ Icc ((L + dist (f z) (p um) - G) - 4 * δ - 2 * 0) (L + dist (f z) (p um) - G))
        ∧ (∀ r ∈ Icc um ym, dist (p um) (p r) ≤ L + dist (f z) (p um) - G) := by
      refine quasi_convex_projection_small_gaps (f := f) (G := H) ?_ hz.1 ?_ (fun t _ ↦ hp t) hδ ?_
      · exact hf.mono (Icc_subset_Icc (by rfl) hz.2)
      · exact h_H'.quasiconvex
      · refine ⟨?_, ?_⟩
        · linarith only [hδ₀, h_fz_pum_G]
        · simp only [dist_comm, pz] at hz_um_uM_L ⊢
          linarith only [hz_um_uM_L]
    refine ⟨ym, hym.1, ?_, ?_⟩
    · linarith only [hym.2.1.1, h_fz_pum_G]
    · intro x hx
      have h₁ := h_H.dist_eq (pH x)
      have h₂ := h_H.dist_eq (pH um)
      have h₃ := hym.2.2 x hx
      have h₄ := dist_triangle m (p um) (p x)
      simp only [dist_comm] at h₁ h₂ h₃ h₄ ⊢
      linarith only [h₁, h₂, h₃, h₄]
  have h_um_ym_subset : Icc um ym ⊆ Icc um uM := Icc_subset_Icc (by rfl) (hym.2.trans hz.2)

  /- Choose a point `cm` between `f um` and `f ym` realizing the minimal distance to `H`.
  Call this distance `dm`. -/
  obtain ⟨closestm, hclosestm⟩ :
      ∃ closestm ∈ Icc um ym, ∀ v ∈ Icc um ym, infDist (f closestm) H ≤ infDist (f v) H := by
    have : ContinuousOn (fun r ↦ infDist (f r) H) (Icc um ym) :=
      continuous_infDist_pt H |>.comp_continuousOn (hf.mono h_um_ym_subset)
    refine IsCompact.exists_isMinOn ?_ ?_ this
    · exact isCompact_Icc
    · rw [nonempty_Icc]
      exact hym.1
  let dm : ℝ := infDist (f closestm) H

  -- Same things but in the interval $[z, uM]$.

  -- The point `p uM` lies at nearly at the `m`- end of the geodesic `H` (at least a distance `G`
  -- from `f z`)
  have h_fz_puM_G : G ≤ dist (f z) (p uM) := by
    have :=
    calc dist (f uM) (f z) ≤ dist (f uM) (p uM) + dist (p uM) (f z) := dist_triangle ..
      _ ≤ dist (f uM) m + dist (p uM) (f z) := by
        gcongr
        exact projSet_dist_le h_H.right_mem (hp uM)
    simp only [G, gromovProductAt, dist_comm] at I this ⊢
    linarith only [I.1, I.2, this]

  -- Choose a point `f yM` to the right of `f z` whose projection on `H` is roughly at distance
  -- `G - L` of `f z`.
  obtain ⟨yM, hyM, hyM_dist, hyM₂⟩ : ∃ yM ∈ Icc z uM,
      L - 4 * δ ≤ dist (p uM) (p yM) ∧ ∀ x ∈ Icc yM uM, G ≤ dist (f z) (p x) + L := by
    obtain ⟨yM, hyM⟩ : ∃ yM ∈ Icc z uM,
        (dist (p uM) (p yM)
          ∈ Icc ((L + dist (f z) (p uM) - G) - 4 * δ - 2 * 0) (L + dist (f z) (p uM) - G))
        ∧ (∀ r ∈ Icc yM uM, dist (p uM) (p r) ≤ L + dist (f z) (p uM) - G) := by
      refine quasi_convex_projection_small_gaps' (f := f) (G := H) ?_ hz.2 ?_ (fun t _ ↦ hp t) hδ ?_
      · exact hf.mono (Icc_subset_Icc hz.1 (le_refl _))
      · exact h_H'.quasiconvex
      · refine ⟨?_, ?_⟩
        · linarith only [hδ₀, h_fz_puM_G]
        · simp only [pz] at hz_um_uM_L ⊢
          linarith only [hz_um_uM_L]
    refine ⟨yM, hyM.1, ?_, ?_⟩
    · linarith only [hyM.2.1.1, h_fz_puM_G]
    · intro x hx
      have h₁ := h_H.dist_eq (pH x)
      have h₂ := h_H.dist_eq (pH uM)
      have h₃ := hyM.2.2 x hx
      have h₄ := dist_triangle m (p uM) (p x)
      simp only [dist_comm] at h₁ h₂ h₃ h₄ ⊢
      linarith only [h₁, h₂, h₃, h₄]

  have h_yM_uM_subset : Icc yM uM ⊆ Icc um uM := Icc_subset_Icc (hz.1.trans hyM.1) (le_refl _)

  /- Choose a point `cM` between `f uM` and `f yM` realizing the minimal distance to `H`.
  Call this distance `dm`. -/
  obtain ⟨closestM, hclosestM⟩ :
      ∃ closestM ∈ Icc yM uM, ∀ v ∈ Icc yM uM, infDist (f closestM) H ≤ infDist (f v) H := by
    have : ContinuousOn (fun r ↦ infDist (f r) H) (Icc yM uM) :=
      continuous_infDist_pt H |>.comp_continuousOn (hf.mono h_yM_uM_subset)
    refine isCompact_Icc.exists_isMinOn ?_ this
    rw [nonempty_Icc]
    exact hyM.2
  let dM : ℝ := infDist (f closestM) H
  have : 0 ≤ dM := infDist_nonneg

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
          have h₁ := hym₂ _ hrm
          have h₂ := hyM₂ _ hrM
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
    have h₃m := hym₂ _ hrm
    have h₃M := hyM₂ _ hrM
    have A : G - L - 2 * deltaG X ≤ gromovProductAt (f z) (f rm) (p rm) := by
      have h₁ : dist (f rm) (p rm) + dist (p rm) (f z) ≤ dist (f rm) (f z) + 4 * deltaG X :=
        dist_along_geodesic h_H' (hp _) h_H.left_mem
      simp only [gromovProductAt, dist_comm] at h₁ h₃m ⊢
      linarith only [h₁, h₃m]
    have B : G - L - 2 * deltaG X ≤ gromovProductAt (f z) (p rM) (f rM) := by
      have h₁ : dist (f rM) (p rM) + dist (p rM) (f z) ≤ dist (f rM) (f z) + 4 * deltaG X :=
        dist_along_geodesic h_H' (hp _) h_H.left_mem
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
  clear hym₂ hyM₂

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
              . linarith only [hδ₀]
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

  obtain I₂ | I₂ := le_or_gt dM dm
  · have I₁ : dm ≥ D + 4 * C := by
      rw [not_and_or] at h
      push_neg at h
      obtain I₁ | I₁ := h <;> linarith only [I₁, I₂]

    have : 0 < dm := by linarith only [I₁, hC, hδ₀]
    obtain ⟨v, hv₁, A⟩ : ∃ v ∈ Icc um ym,
      L - 13 * δ
        ≤ (4 * exp (1/2 * log 2)) * Λ * exp (-((1-α) * D * log 2 / (5 * δ))) * ((ym - v)
            * exp (-(α * max dm ((dist (f v) (p v) + dm) / 4) * log 2 / (5 * δ)))) := by
      refine Morse_Gromov_theorem_aux_m (hf.mono ?_) hC ?_ ?_ hym.1 h_H' hδ hp dm ?_ I₁ hym_dist
      · exact h_um_ym_subset
      · positivity
      · intro s t hs ht
        exact hf'.upper_bound (h_um_ym_subset hs) (h_um_ym_subset ht)
      · exact hclosestm.2

    set M : ℝ := max dm ((dist (f v) (p v) + dm) / 4)
    have : _ ≤ M := le_max_left ..
    have : _ ≤ M := le_max_right ..

    have aux2 : L + C + 2 * δ ≤ ((L + 2 * δ)/D) * dm := by
      have h₁ :=
      calc L + C = (L/D) * (D + (D/L) * C) := by field_simp; ring
        _ ≤ (L/D) * (D + 4 * C) := by
            gcongr
            rw [div_le_iff]
            · linarith only [hδ₀]
            positivity
        _ ≤ (L/D) * dm := by gcongr
      have h₂ :=
      calc 2 * δ = (2 * δ) / D * D := by field_simp
        _ ≤ (2 * δ)/D * dm := by
            gcongr
            linarith only [I₁, hC]
      rw [add_div, add_mul]
      linarith only [h₁, h₂]

    /- Substep 1: We can control the distance from `f v` to `f closestM` in terms of the distance
    of the distance of `f v` to `H`, i.e., by `2^k * dm`. The same control follows
    for `closestM - v` thanks to the quasi-isometry property. Then, we massage this
    inequality to put it in the form we will need, as an upper bound on `(x-v) * exp (-2^k * dm)`. -/
    have :=
    calc |v - closestM| ≤ Λ * (infDist (f v) H + (L + C + 2 * δ) + infDist (f closestM) H) :=
          hD hv₁ hclosestM.1
      _ ≤ Λ * (dist (f v) (p v) + (L + C + 2 * δ) + dM) := by
          gcongr
          rw [← (hp v).2]
      _ = Λ * (dist (f v) (p v) + dM + (L + C + 2 * δ)) := by ring
      _ ≤ Λ * (dist (f v) (p v) + dm + ((L + 2 * δ)/D) * dm) := by gcongr
      _ = Λ * ((dist (f v) (p v) + dm) / 4 * 4 + ((L + 2 * δ)/D) * dm) := by ring
      _ ≤ Λ * (M * 4 + ((L + 2 * δ)/D) * M) := by gcongr
      _ = Λ * (4 + ((L + 2 * δ)/D)) * M := by ring
    have : |v - closestM| / (Λ * (4 + (L + 2 * δ)/D)) ≤ M := by
      rw [div_le_iff]
      convert this using 1
      · ring
      · positivity
    /- We reformulate this control inside of an exponential, as this is the form we
    will use later on. -/
    have :=
    calc exp (- (α * M * log 2 / (5 * δ)))
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
          linarith only [hv₁.2, hym.2, hyM.1, hclosestM.1.1]
    have : 0 ≤ ym - v := by linarith only [hv₁.2]
    -- Plug in `ym-v` to get the final form of this inequality.
    have :=
    calc K * (ym - v) * exp (- (α * M * log 2 / (5 * δ)))
        ≤ K * (ym - v) * exp (-K * (closestM - v)) := by gcongr
      _ = ((K * (ym - v) + 1) - 1) * exp (- K * (closestM - v)) := by ring
      _ ≤ (exp (K * (ym - v)) - 1) * exp (-K * (closestM - v)) := by gcongr; apply add_one_le_exp
      _ = exp (-K * (closestM - ym)) - exp (-K * (closestM - v)) := by
          rw [sub_mul, ← exp_add]
          ring_nf
      _ ≤ exp (-K * (closestM - ym)) - exp (-K * (uM - um)) := by
          gcongr _ - exp ?_
          apply mul_le_mul_of_nonpos_left
          · linarith only [hv₁.1, hclosestM.1.2]
          rw [Left.neg_nonpos_iff]
          positivity
    have B : (ym - v) * exp (- (α * M * log 2 / (5 * δ)))
        ≤ (exp (-K * (closestM - ym)) - exp (-K * (uM-um)))/K := by
      rw [le_div_iff]
      · convert this using 1
        ring
      positivity
    -- End of substep 1

    /- Use the second substep to show that `ym-v` is bounded below, and therefore
    that `closestM - ym` (the endpoints of the new geodesic we want to consider in the
    inductive argument) are quantitatively closer than `uM - um`, which means that we
    will be able to use the inductive assumption over this new geodesic. -/
    have :=
    calc L - 13 * δ
        ≤ (4 * exp (1/2 * log 2)) * Λ * exp (-((1-α) * D * log 2 / (5 * δ))) * ((ym - v) * exp (-(α * M * log 2 / (5 * δ)))) := A
      _ ≤ (4 * exp (1/2 * log 2)) * Λ * exp 0 * ((ym - v) * exp 0) := by
          gcongr
          · rw [Left.neg_nonpos_iff]
            positivity
          · rw [Left.neg_nonpos_iff]
            positivity
      _ = (4 * exp (1/2 * log 2)) * Λ * (ym-v) := by simp
      _ ≤ 20 * Λ * (ym - v) := by
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
    have : (1/4) * δ / Λ ≤ ym - v := by
      rw [div_le_iff]
      · linarith only [this]
      positivity
    have :=
    calc (1/4) * δ / Λ
        ≤ - v + ym := by linarith only [this]
      _ ≤ uM - um + ym - closestM := by linarith only [hclosestM.1.2, hv₁.1]
    -- start to set up for the well-founded induction
    have h₂ : z ∈ Icc ym closestM :=
      ⟨hym.2, by linarith only [hyM.1, hclosestM.1.1]⟩
    have h₁ : ym ≤ closestM := h₂.1.trans h₂.2
    have : Nat.floor (4 * Λ * |closestM - ym| / δ) < Nat.floor (4 * Λ * |uM - um| / δ) := by
      calc Nat.floor (4 * Λ * |closestM - ym| / δ) < Nat.floor (4 * Λ * |closestM - ym| / δ + 1) := by
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
    have : 0 < L - 13 * δ := by
      ring_nf
      positivity
    have H₂ :=
    calc L + 4 * δ = ((L + 4 * δ)/(L - 13 * δ)) * (L - 13 * δ) := by field_simp
      _ ≤ ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp (1/2 * log 2)) * Λ
          * exp (- ((1 - α) * D * log 2 / (5 * δ))) * ((ym - v)
          * exp (- (α * M * log 2 / (5 * δ))))) := by rel [A]
      _ ≤ ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp (1/2 * log 2)) * Λ
          * exp (- ((1 - α) * D * log 2 / (5 * δ)))
          * ((exp (-K * (closestM - ym)) - exp (-K * (uM - um)))/K)) := by rel [B]
      _ = Kmult * (exp (-K * (closestM - ym)) - exp (-K * (uM - um))) := by
          dsimp [Kmult]
          ring

    calc gromovProductAt (f z) (f um) (f uM)
        ≤ gromovProductAt (f z) (f ym) (f closestM) + (L + 4 * δ) := by
          refine Rec ?_ hclosestM.1
          simp [hym.1]
      _ ≤ (Λ ^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ
          + Kmult * (1 - exp (- K * (closestM - ym))))
          + (Kmult * (exp (-K * (closestM - ym)) - exp (-K * (uM-um)))) := by
          have h₃ : Icc ym closestM ⊆ Icc um uM := by
            rw [Icc_subset_Icc_iff h₁]
            exact ⟨hym.1, hclosestM.1.2⟩
          have := Morse_Gromov_theorem_aux0 (hf.mono h₃) (hf'.mono h₃) h₁ h₂ hδ
          dsimp [K, Kmult] at this H₂ ⊢
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

    obtain ⟨v, hv₁, A⟩ : ∃ v ∈ Icc yM uM,
        L - 13 * δ
        ≤ (4 * exp (1/2 * log 2)) * Λ * exp (-((1-α) * D * log 2 / (5 * δ))) * ((v - yM)
          * exp (-(α * max dM ((dist (f v) (p v) + dM) / 4) * log 2 / (5 * δ)))) := by
      refine Morse_Gromov_theorem_aux_M (hf.mono ?_) hC ?_ ?_ hyM.2 h_H' hδ hp dM ?_ I₁ hyM_dist
      · exact h_yM_uM_subset
      · positivity
      · intro s t hs ht
        exact hf'.upper_bound (h_yM_uM_subset hs) (h_yM_uM_subset ht)
      · exact hclosestM.2

    set M : ℝ := max dM ((dist (f v) (p v) + dM) / 4)
    have : _ ≤ M := le_max_left ..
    have : _ ≤ M := le_max_right ..

    have aux2 : L + C + 2 * δ ≤ ((L + 2 * δ)/D) * dM := by
      have h₁ :=
      calc L + C = (L/D) * (D + (D/L) * C) := by field_simp; ring
        _ ≤ (L/D) * (D + 4 * C) := by
            gcongr
            rw [div_le_iff]
            · linarith only [hδ₀]
            positivity
        _ ≤ (L/D) * dM := by gcongr
      have h₂ :=
      calc 2 * δ = (2 * δ) / D * D := by field_simp
        _ ≤ (2 * δ)/D * dM := by
            gcongr
            linarith only [I₁, hC]
      rw [add_div, add_mul]
      linarith only [h₁, h₂]

    /- Substep 1: We can control the distance from `f v` to `f closestm` in terms of the distance
    of the distance of `f v` to `H`, i.e., by `2^k * dM`. The same control follows
    for `v - closestm` thanks to the quasi-isometry property. Then, we massage this
    inequality to put it in the form we will need, as an upper bound on `(x-v) * exp (-2^k * dM)`. -/
    have :=
    calc |closestm - v| ≤ Λ * (infDist (f closestm) H + (L + C + 2 * δ) + infDist (f v) H) :=
          hD hclosestm.1 hv₁
      _ ≤ Λ * (dm + (L + C + 2 * δ) + dist (f v) (p v)) := by
          gcongr
          rw [← (hp v).2]
      _ = Λ * ((L + C + 2 * δ) + dist (f v) (p v) + dm) := by ring
      _ ≤ Λ * ((((L + 2 * δ)/D) * dM) + dist (f v) (p v) + dM) := by gcongr
      _ = Λ * ((((L + 2 * δ)/D) * dM) + (dist (f v) (p v) + dM) / 4 * 4) := by ring
      _ ≤ Λ * ((((L + 2 * δ)/D) * M) + M * 4) := by gcongr
      _ = Λ * (4 + (L + 2 * δ)/D) * M := by ring
    have : |v - closestm| / (Λ * (4 + (L + 2 * δ)/D)) ≤ M := by
      rw [div_le_iff]
      convert this using 1
      · rw [abs_sub_comm]
      · ring
      · positivity
    /- We reformulate this control inside of an exponential, as this is the form we
    will use later on. -/
    have :=
    calc exp (- (α * M * log 2 / (5 * δ)))
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
          linarith only [hv₁.1, hyM.1, hym.2, hclosestm.1.2]
    have : 0 ≤ v - yM := by linarith only [hv₁.1]
    -- Plug in `v - yM` to get the final form of this inequality.
    have :=
    calc K * (v - yM) * exp (- (α * M * log 2 / (5 * δ)))
        ≤ K * (v - yM) * exp (-K * (v - closestm)) := by gcongr
      _ = ((K * (v - yM) + 1) - 1) * exp (- K * (v - closestm)) := by ring
      _ ≤ (exp (K * (v - yM)) - 1) * exp (-K * (v - closestm)) := by gcongr; apply add_one_le_exp
      _ = exp (-K * (yM - closestm)) - exp (-K * (v - closestm)) := by
          rw [sub_mul, ← exp_add]
          ring_nf
      _ ≤ exp (-K * (yM - closestm)) - exp (-K * (uM - um)) := by
          gcongr _ - exp ?_
          apply mul_le_mul_of_nonpos_left
          · linarith only [hv₁.2, hclosestm.1.1]
          rw [Left.neg_nonpos_iff]
          positivity
    have B : (v - yM) * exp (- (α * M * log 2 / (5 * δ)))
        ≤ (exp (-K * (yM - closestm)) - exp (-K * (uM-um)))/K := by
      rw [le_div_iff]
      · convert this using 1
        ring
      positivity
    -- End of substep 1

    /- Use the second substep to show that `yM-v` is bounded below, and therefore
    that `closestM - yM` (the endpoints of the new geodesic we want to consider in the
    inductive argument) are quantitatively closer than `uM - um`, which means that we
    will be able to use the inductive assumption over this new geodesic. -/
    have :=
    calc L - 13 * δ
        ≤ (4 * exp (1/2 * log 2)) * Λ * exp (-((1-α) * D * log 2 / (5 * δ))) * ((v - yM) * exp (-(α * M * log 2 / (5 * δ)))) := A  --
      _ ≤ (4 * exp (1/2 * log 2)) * Λ * exp 0 * ((v - yM) * exp 0) := by
          gcongr
          · rw [Left.neg_nonpos_iff]
            positivity
          · rw [Left.neg_nonpos_iff]
            positivity
      _ = (4 * exp (1/2 * log 2)) * Λ * (v-yM) := by simp
      _ ≤ 20 * Λ * (v - yM) := by
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
    have : (1/4) * δ / Λ ≤ v - yM := by
      rw [div_le_iff]
      · linarith only [this]
      positivity
    have :=
    calc (1/4) * δ / Λ
        ≤ v - yM := by linarith only [this]
      _ ≤ uM - um - yM + closestm := by linarith only [hclosestm.1.1, hv₁.2]

    -- start to set up for the well-founded induction
    have h₂ : z ∈ Icc closestm yM :=
      ⟨by linarith only [hym.2, hclosestm.1.2], by linarith only [hyM.1]⟩
    have h₁ : closestm ≤ yM := h₂.1.trans h₂.2
    have : Nat.floor (4 * Λ * |yM - closestm| / δ) < Nat.floor (4 * Λ * |uM - um| / δ) := by
      calc Nat.floor (4 * Λ * |yM - closestm| / δ) < Nat.floor (4 * Λ * |yM - closestm| / δ + 1) := by
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
    have : 0 < L - 13 * δ := by
      ring_nf
      positivity
    have H₂ :=
    calc L + 4 * δ = ((L + 4 * δ)/(L - 13 * δ)) * (L - 13 * δ) := by field_simp
      _ ≤ ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp (1/2 * log 2)) * Λ
          * exp (- ((1 - α) * D * log 2 / (5 * δ))) * ((v - yM)
          * exp (- (α * M * log 2 / (5 * δ))))) := by gcongr
      _ ≤ ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp (1/2 * log 2)) * Λ
          * exp (- ((1 - α) * D * log 2 / (5 * δ)))
          * ((exp (-K * (yM - closestm)) - exp (-K * (uM - um)))/K)) := by gcongr
      _ = Kmult * (exp (-K * (yM - closestm)) - exp (-K * (uM - um))) := by
          dsimp [Kmult]
          ring

    calc gromovProductAt (f z) (f um) (f uM)
        ≤ gromovProductAt (f z) (f closestm) (f yM) + (L + 4 * δ) := by
          apply Rec hclosestm.1
          simp [hyM.2]
      _ ≤ (Λ ^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ
          + Kmult * (1 - exp (- K * (yM - closestm))))
          + (Kmult * (exp (-K * (yM - closestm)) - exp (-K * (uM-um)))) := by
          have h₃ : Icc closestm yM ⊆ Icc um uM := by
            rw [Icc_subset_Icc_iff h₁]
            exact ⟨hclosestm.1.1, hyM.2⟩
          have := Morse_Gromov_theorem_aux0 (hf.mono h₃) (hf'.mono h₃) h₁ h₂ hδ
          dsimp [K, Kmult] at this H₂ ⊢
          linarith only [this, H₂]
      _ = (Λ^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (uM - um)))) := by
          dsimp [K]
          ring
    -- end of the case where `D + 4 * C ≤ dM` and `dm ≤ dM`.
termination_by Nat.floor (4 * Λ * |uM - um| / δ)
