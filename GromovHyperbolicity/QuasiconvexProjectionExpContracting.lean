/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD -/
import GromovHyperbolicity.Quasiconvex
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Set Metric Real Classical

/-! The main result of this file is `quasiconvex_projection_exp_contracting`, a key technical result
used in the Gouëzel-Shchur quantitative Morse lemma. -/

variable {X : Type*} [MetricSpace X] [Gromov_hyperbolic_space X] [GeodesicSpace X]

open Gromov_hyperbolic_space BigOperators

variable {G : Set X}

/-- The next lemma (for `C = 0`, Lemma 2 in~\<^cite> "shchur") asserts that, if two points are not too far apart (at distance at most
`10 * δ`), and far enough from a given geodesic segment, then when one moves towards this
geodesic segment by a fixed amount (here `5 * δ`), then the two points become closer (the new
distance is at most `5 * δ`, gaining a factor of `2`). Later, we will iterate this lemma to
show that the projection on a geodesic segment is exponentially contracting. For the application,
we give a more general version involving an additional constant `C`.

This lemma holds for `δ` the hyperbolicity constant. We will want to apply it with `δ > 0`,
so to avoid problems in the case `δ = 0` we formulate it not using the hyperbolicity constant of
the given type, but any constant which is at least the hyperbolicity constant (this is to work
around the fact that one can not say or use easily in Isabelle that a type with hyperbolicity
`δ` is also hyperbolic for any larger constant `δ'`. -/
lemma geodesic_projection_exp_contracting_aux (hG : geodesic_segment G) {x y px py : X}
    (hpxG : px ∈ proj_set x G) (hpyG : py ∈ proj_set y G) {δ C : ℝ}
    (hδ : δ ≥ deltaG X) {M : ℝ} (hxy : dist x y ≤ 10 * δ + C)
    (hM : M ≥ 15/2 * δ) (hpx : M + 5 * δ + C/2 ≤ dist px x) (hpy : M + 5 * δ + C/2 ≤ dist py y)
    (hC : C ≥ 0) :
    dist (geodesic_segment_param {px‒x} px M) (geodesic_segment_param {py‒y} py M) ≤ 5 * δ := by
  have hpxpyx : dist px x ≤ dist py x := by
    simpa only [dist_comm] using proj_set_dist_le hpyG.1 hpxG
  have hpypxy : dist py y ≤ dist px y := by
    simpa only [dist_comm] using proj_set_dist_le hpxG.1 hpyG
  have hδ₀ : 0 ≤ δ := by
    have : Inhabited X := ⟨x⟩
    linarith only [hδ, delta_nonneg X]
  have hM' : 0 ≤ M ∧ M ≤ dist px x ∧ M ≤ dist px y ∧ M ≤ dist py x ∧ M ≤ dist py y := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have : px ∈ G ∧ py ∈ G := ⟨hpxG.1, hpyG.1⟩
  set x' := geodesic_segment_param {px‒x} px M
  set y' := geodesic_segment_param {py‒y} py M
  /- First step: the distance between `px` and `py` is at most `5 * δ`. -/
  have hpxpyδ :=
  calc dist px py
      ≤ max (5 * deltaG X) (dist x y - dist px x - dist py y + 10 * deltaG X) :=
        proj_along_geodesic_contraction hG hpxG hpyG
    _ ≤ max (5 * deltaG X) (5 * deltaG X) := by
        gcongr
        linarith only [hδ, hxy, hpx, hpy, hM, hδ₀]
    _ ≤ 5 * δ := by
        rw [max_self]
        gcongr
  /- Second step: show that all the interesting Gromov products at bounded below by `M`. -/
  have hx'_mem : x' ∈ {px‒x} := geodesic_segment_param_in_segment (some_geodesic_endpoints).2.2
  have : px ∈ proj_set x' G := by
    refine proj_set_geodesic_same_basepoint hpxG (G := {px‒x}) ?_ hx'_mem
    exact (some_geodesic_is_geodesic_segment _ _).1
  have hpxx'M : dist px x' = M := by
    apply geodesic_segment_param_in_geodesic_spaces6
    exact ⟨hM'.1, hM'.2.1⟩
  have hpxpyx' : dist px x' ≤ dist py x' := by
    simpa only [dist_comm] using proj_set_dist_le hpyG.1 this
  have : dist px x = dist px x' + dist x' x := by
    rw [← geodesic_segment_dist (some_geodesic_is_geodesic_segment px x).1 hx'_mem]
  have Ixx : Gromov_product_at px x' x = M := by
    dsimp only [Gromov_product_at]
    linarith only [this, hpxx'M]
  have Iyx : Gromov_product_at py x x' ≥ M := by
    simp only [Gromov_product_at, dist_comm] at Ixx hpxpyx hpxpyx' ⊢
    linarith only [Ixx, hpxpyx, hpxpyx']
  have hy'_mem : y' ∈ {py‒y} := geodesic_segment_param_in_segment (some_geodesic_endpoints).2.2
  have : py ∈ proj_set y' G := by
    refine proj_set_geodesic_same_basepoint hpyG (G := {py‒y}) ?_ hy'_mem
    exact (some_geodesic_is_geodesic_segment _ _).1
  have hpyy'M : dist py y' = M := by
    apply geodesic_segment_param_in_geodesic_spaces6
    exact ⟨hM'.1, hM'.2.2.2.2⟩
  have hpypyy' : dist py y' ≤ dist px y' := by
    simpa only [dist_comm] using proj_set_dist_le hpxG.1 this
  have : dist py y = dist py y' + dist y' y := by
    rw [← geodesic_segment_dist (some_geodesic_is_geodesic_segment py y).1 hy'_mem]
  have Iyy : Gromov_product_at py y' y = M := by
    dsimp only [Gromov_product_at]
    linarith only [this, hpyy'M]
  have Ixy : Gromov_product_at px y y' ≥ M := by
    simp only [Gromov_product_at, dist_comm] at Iyy hpypxy hpypyy' ⊢
    linarith only [Iyy, hpypxy, hpypyy']
  have Ix : Gromov_product_at px x y ≥ M := by
    dsimp only [Gromov_product_at]
    linarith only [hpypxy, hxy, hpx, hpy]
  have Iy : Gromov_product_at py x y ≥ M := by
    dsimp only [Gromov_product_at] at *
    linarith only [hpxpyx, hxy, hpx, hpy]
  /- Third step: prove the estimate -/
  have A : M - 4 * δ + dist x' y' ≤ dist px y' := by
    have h₁ := le_min Ixx.ge <| le_min Ix Ixy
    have h₂ : _ ≤ _ / 2 := hyperb_ineq_4_points px x' x y y'
    linarith only [hpxx'M, hδ, h₁, h₂]
  have B : M - 4 * δ + dist x' y' ≤ dist py x' := by
    rw [Gromov_product_commute] at Iyx Iyy
    have h₁ := le_min Iyx.le <| le_min Iy Iyy.ge
    have h₂ : _ ≤ _ / 2 := hyperb_ineq_4_points py x' x y y'
    linarith only [hpyy'M, hδ, h₁, h₂]
  have hpxpy : dist px py ≤ 2 * M - 10 * δ := by linarith only [hpxpyδ, hM]
  have : 2 * M - 10 * δ + 2 * dist x' y'
      ≤ max (dist px py + dist y' x') (dist px x' + dist y' py) := by
    have := hyperb_quad_ineq px y' py x'
    linarith only [this, hδ, A, B]
  have : 2 * M - 10 * δ + 2 * dist x' y' ≤ dist px x' + dist py y' := by
    simp only [dist_comm] at this hpxpy hpxx'M hpyy'M
    rw [le_max_iff] at this
    obtain h | h := this <;> linarith only [this, hpxpy, h, hδ₀, hpxx'M, hpyy'M]
  linarith only [hpxx'M, hpyy'M, this]

attribute [-simp] mul_eq_mul_left_iff -- FIXME global?

/-- The next lemma (Lemma 10 in~\<^cite>\<open>"shchur"\<close> for `C = 0`) asserts that the projection on a geodesic segment is
an exponential contraction.
More precisely, if a path of length `L` is at distance at least `D` of a geodesic segment `G`,
then the projection of the path on `G` has diameter at most `C * L * exp (-c * D / δ)`, where `C` and
`c` are universal constants. This is not completely true at one can not go below a fixed size, as
always, so the correct bound is `K * max δ (L * exp (-c * D / δ))`. For the application, we
give a slightly more general statement involving an additional constant `C`.

This statement follows from the previous lemma: if one moves towards `G` by `10 * δ`, then
the distance between points is divided by `2`. Then one iterates this statement as many times
as possible, gaining a factor `2` each time and therefore an exponential factor in the end. -/
-- TODO don't know if notation is Ioo or Icc
lemma geodesic_projection_exp_contracting (hG : geodesic_segment G) {f : ℝ → X} {a b Λ C : ℝ}
    (h : ∀ x y, x ∈ Icc a b → y ∈ Icc a b → dist (f x) (f y) ≤ Λ * |x - y| + C) -- NB changed from `dist x y` in original
    (hab : a ≤ b) {pa : X} (hpa : pa ∈ proj_set (f a) G) {pb : X} (hpb : pb ∈ proj_set (f b) G)
    {D : ℝ} (hG' : ∀ t, t ∈ Icc a b → infDist (f t) G ≥ D) {δ : ℝ} (hD : D ≥ 15/2 * δ + C/2)
    (hδ : δ > deltaG X) (hC : C ≥ 0) (hΛ : Λ ≥ 0) :
    dist pa pb ≤ max (5 * deltaG X)
      ((4 * exp (1/2 * log 2)) * Λ * (b-a) * exp (-(D-C/2) * log 2 / (5 * δ))) := by
  have : Inhabited X := ⟨pa⟩
  have hδ₀ : δ > 0 := by
    linarith only [delta_nonneg X, hδ]
  have :=
  calc exp (15/2/5 * log 2) = exp (log 2) * exp (1/2 * log (2:ℝ)) := by
        rw [← exp_add]
        ring_nf
    _ = 2 * exp (1/2 * log 2) := by rw [exp_log]; norm_num
  have hab' : 0 ≤ b - a := by linarith only [hab]

  /- The idea of the proof is to start with a sequence of points separated by `10 * δ + C` along
  the original path, and push them by a fixed distance towards `G` to bring them at distance at most
  `5 * δ`, thanks to the previous lemma. Then, discard half the points, and start again. This
  is possible while one is far enough from `G`. In the first step of the proof, we formalize this
  in the case where the process can be iterated long enough that, at the end, the projections on `G`
  are very close together. This is a simple induction, based on the previous lemma. -/
  have Main (k : ℕ) : ∀ c (g : ℕ → X) (p : ℕ → X),
              (∀ i ≤ (2^k), p i ∈ proj_set (g i) G)
            → (∀ i ≤ (2^k), 5 * δ * k + 15/2 * δ + c/2 ≤ dist (p i) (g i))
            → (∀ i < (2^k), dist (g i) (g (i + 1)) ≤ 10 * δ + c)
            → c ≥ 0
            → dist (p 0) (p (2^k)) ≤ 5 * deltaG X := by
    induction' k with k IH
    · intro c g p hp hpg hg _
      have H : p 0 ∈ proj_set (g 0) G ∧ p 1 ∈ proj_set (g 1) G ∧ dist (g 0) (g 1) ≤ 10 * δ + c
          ∧ 15/2 * δ + c/2 ≤ dist (p 0) (g 0) ∧ 15/2 * δ + c/2 ≤ dist (p 1) (g 1) := by
        refine ⟨hp _ ?_, hp _ ?_, hg _ ?_, ?_, ?_⟩
        · simp
        · simp
        · simp
        · convert hpg 0 (by simp) using 1
          simp
        · convert hpg 1 (by simp) using 1
          simp
      calc dist (p 0) (p 1)
          ≤ max (5 * deltaG X)
            (dist (g 0) (g 1) - dist (p 0) (g 0) - dist (p 1) (g 1) + 10 * deltaG X) :=
            proj_along_geodesic_contraction hG H.1 H.2.1
        _ ≤ max (5 * deltaG X)
            ((10 * δ + c) - (15/2 * δ + c/2) - (15/2 * δ + c/2) + 10 * deltaG X) := by
            have := H.2.2.1
            have := H.2.2.2.1
            have := H.2.2.2.2
            gcongr
        _ ≤ max (5 * deltaG X) (5 * deltaG X) := by
            gcongr
            linarith only [hδ]
        _ = 5 * deltaG X := by simp
    intro c g p hp hpg hg hc
    have : 5 * δ * (k + 1) + 5 * δ = 5 * δ * (k + 2) := by ring
    let h : ℕ → X := fun i ↦ geodesic_segment_param {(p i)‒(g i)} (p i) (5 * δ * k + 15/2 * δ)
    have hi' {i : ℕ} : i ≤ (2 ^ k) → 2 * i ≤ (2 ^ (k + 1)) := by
      intro h
      ring_nf
      linarith only [h]
    have h_dist (i : ℕ) (hi : i < (2 ^ (k + 1))) : dist (h i) (h (i + 1)) ≤ 5 * δ := by
      dsimp [h]
      apply geodesic_projection_exp_contracting_aux hG (hp _ ?_) (hp _ ?_) hδ.le (hg _ ?_) ?_ ?_ ?_ hc
      · exact hi.le
      · exact hi
      · exact hi
      · have : 0 ≤ 5 * δ * k := by positivity
        linarith only [this]
      · convert (hpg i ?_) using 1
        · push_cast
          ring
        · exact hi.le
      · convert (hpg _ ?_) using 1
        · push_cast
          ring
        · exact hi
    let g' : ℕ → X := fun i ↦ h (2 * i)
    let p' : ℕ → X := fun i ↦ p (2 * i)
    calc dist (p 0) (p (2 ^ (k + 1))) = dist (p' 0) (p' (2 ^ k)) := by dsimp [p']; ring_nf
      _ ≤ 5 * deltaG X := ?_
    refine IH 0 g' p' ?_ ?_ ?_ (by rfl)
    · intro i hi
      dsimp [p', g', h]
      apply proj_set_geodesic_same_basepoint (hp _ (hi' hi)) (G := {p (2 * i)‒g (2 * i)})
      · exact (some_geodesic_is_geodesic_segment _ _).1
      · apply geodesic_segment_param_in_segment
        exact some_geodesic_endpoints.2.2
    · intro i hi
      dsimp [p', g', h]
      rw [geodesic_segment_param_in_geodesic_spaces6]
      · linarith only []
      refine ⟨by positivity, ?_⟩-- rfl
      calc 5 * δ * k + 15/2 * δ
          ≤ 5 * δ * (k + 1) + 15/2 * δ + c/2 := by linarith only [hc, hδ₀]
        _ ≤ dist (p (2 * i)) (g (2 * i)) := by convert hpg _ (hi' hi); norm_cast
    · intro i hi
      calc dist (g' i) (g' (i + 1)) = dist (h (2 * i)) (h (2 * i + 1 + 1)) := rfl
        _ ≤ dist (h (2 * i)) (h (2 * i + 1)) + dist (h (2 * i + 1)) (h (2 * i + 1 + 1)) := dist_triangle ..
        _ ≤ 5 * δ + 5 * δ := by
            gcongr <;> apply h_dist <;>
            · ring_nf
              linarith only [hi]
        _ = 10 * δ + 0 := by ring

  /- Now, we will apply the previous basic statement to points along our original path. We
  introduce `k`, the number of steps for which the pushing process can be done -- it only depends on
  the original distance `D` to `G`. -/

  let k : ℕ := Nat.floor ((D - C/2 - 15/2 * δ) / (5 * δ))
  have hk₁ : k ≤ (D - C/2 - 15/2 * δ) / (5 * δ) ∧ (D - C/2 - 15/2 * δ) / (5 * δ) ≤ k + 1 := by
    constructor
    · apply Nat.floor_le
      have : 0 ≤ D - C / 2 - 15 / 2 * δ := by linarith only [hD]
      positivity
    · apply le_of_lt
      norm_cast
      apply Nat.lt_succ_floor
  have hk' : D ≥ 5 * δ * k + 15/2 * δ + C/2 ∧ D ≤ 5 * δ * (k+1) + 15/2 * δ + C/2 := by
    rw [div_le_iff, le_div_iff] at hk₁
    · constructor <;> linarith only [hk₁]
    all_goals positivity
  have hk : 1 / (2^k) ≤ 2 * exp (15/2/5 * log 2) * exp (- ((D-C/2) * log 2 / (5 * δ))) := by
    have :=
    calc exp ((D - C/2) / (5 * δ) * log 2) * exp (-(15/2/5 * log 2))
        = exp (((D - C/2 - 15/2 * δ) / (5 * δ)) * log 2) := by
          rw [← exp_add]
          congr
          field_simp
          ring
      _ ≤ exp ((k+1) * log 2) := by
          gcongr
          exact hk₁.2
      _ = ((2:ℝ) ^ (k+1 : ℝ) : ℝ):= by
          rw [rpow_def_of_pos]
          · ring_nf
          · norm_num
      _ = 2 * 2^k := by norm_cast; ring
    simp only [exp_neg] at this ⊢
    rw [← div_le_one] at this ⊢
    · convert this using 1
      field_simp
      ring
    all_goals positivity

  /- We separate the proof into two cases. If the path is not too long, then it can be covered by
  `2 ^ k` points at distance at most `10 * δ + C`. By the basic statement, it follows that the diameter
  of the projection is at most `5 * δ`. Otherwise, we subdivide the path into `2 ^ N` points at
  distance at most `10 * δ + C`, with `N ≥ k`, and apply the basic statement to blocks of `2 ^ k`
  consecutive points. It follows that the projections of $g_0, g_{2^k}, g_{2\cdot 2^k},\dotsc$ are
  at distances at most `5 * δ`. Hence, the first and last projections are at distance at most
  `2 ^ (N - k) * 5 * δ`, which is the desired bound. -/

  have hi_mem {k i : ℕ} (hi : i ≤ (2 ^ k)) : a + (b-a) * i/2^k ∈ Icc a b := by
    dsimp [Icc]
    constructor
    · have : 0 ≤ (b - a) * i / 2 ^ k := by positivity
      linarith only [this]
    · calc a + (b - a) * i / 2 ^ k ≤ a + (b - a) * 2 ^ k / 2 ^ k := by gcongr; exact_mod_cast hi
        _ = b := by field_simp
  have hG_nonempty (x : X) : (proj_set x G).Nonempty := by
    apply proj_set_nonempty_of_compact
    · apply (geodesic_segment_topology hG).1
    · apply (geodesic_segment_topology hG).2.2.2.2.2
  by_cases h_split : Λ * (b-a) ≤ 10 * δ * 2^k
  · /- First, treat the case where the path is rather short. -/
    let g : ℕ → X := fun i ↦ f (a + (b-a) * i/2^k)
    have hg_endpoints : g 0 = f a ∧ g (2^k) = f b := by simp [g]
    have A (i : ℕ) (hi : i < (2 ^ k)) : dist (g i) (g (i + 1)) ≤ 10 * δ + C := by
      calc dist (g i) (g (i + 1)) ≤ Λ * |(a + (b-a) * i/2^k) - (a + (b-a) * (i + 1)/2^k)| + C := by
            dsimp [g]
            convert h (a + (b - a) * i / 2 ^ k) (a + (b - a) * ↑(i + 1) / 2 ^ k) ?_ ?_
            · norm_cast
            · apply hi_mem hi.le
            · apply hi_mem hi
        _ = Λ * (b - a) / 2 ^ k + C := by
            rw [mul_div_assoc Λ]
            congr
            calc _ = |- ((b - a) / 2 ^ k)| := by
                  congr
                  field_simp
                  ring
              _ = _ := by
                  rw [abs_neg, abs_of_nonneg]
                  positivity
        _ ≤ 10 * δ + C := by
            gcongr
            rwa [div_le_iff]
            positivity
    let p := fun i ↦ if i = 0 then pa else if i = 2^k then pb else (hG_nonempty (g i)).choose
    have B (i : ℕ) (_ : i ≤ (2 ^ k)) : p i ∈ proj_set (g i) G := by
      dsimp only [p]
      split_ifs with hi' hi'
      · rw [hi', hg_endpoints.1]
        exact hpa
      · rw [hi', hg_endpoints.2]
        exact hpb
      · exact (hG_nonempty _).choose_spec
    have C (i : ℕ) (hi : i ≤ (2 ^ k)) : dist (p i) (g i) ≥ 5 * δ * k + 15/2 * δ + C/2 := by
      calc 5 * δ * k + 15/2 * δ + C/2 ≤ D := hk'.1
        _ ≤ infDist (g i) G := hG' _ <| hi_mem hi
        _ = dist (p i) (g i) := by rw [dist_comm, (B i hi).2]
    have : dist (p 0) (p (2^k)) ≤ 5 * deltaG X := Main _ _ g _ B C A hC
    rw [le_max_iff]
    left
    simpa [p] using this

  /- Now, the case where the path is long. We introduce `N` such that it is roughly of length
  `2 ^ N * 10 * δ`. -/
  push_neg at h_split
  have : Λ * (b-a) > 0 := lt_trans (by positivity) h_split
  have : a < b ∧ 0 < Λ := by constructor <;> nlinarith only [this, hΛ, hab]
  let n : ℕ := Nat.floor (log (Λ * (b-a) / (10 * δ)) / log 2)
  have A :=
  calc log (Λ * (b-a) / (10 * δ))
      ≥ log (2^k) := by
        gcongr
        rw [le_div_iff]
        · convert h_split.le using 1
          ring
        · positivity
    _ = k * log 2 := by simp
  have : log (2 ^ n) ≤ log (Λ * (b-a) / (10 * δ)) := by
    have : (n:ℝ) ≤ _ := Nat.floor_le ?_
    rw [le_div_iff] at this
    · simpa using this
    · positivity
    calc _ ≥ (k * log 2) / log 2 := by gcongr
      _ ≥ 0 := by positivity
  have I : 2 ^ n ≤ Λ * (b-a) / (10 * δ) := by
    rwa [log_le_log_iff] at this
    all_goals positivity
  have h₂ : log (Λ * (b-a) / (10 * δ)) < log (2 ^ (n+1)) := by
    have : _ < (↑(n + 1) : ℝ) := Nat.lt_succ_floor _
    rw [div_lt_iff] at this
    · simpa [mul_comm] using this
    positivity
  have J : Λ * (b-a) / (10 * δ) < 2 ^ (n+1) := by
    rwa [log_lt_log_iff] at h₂
    all_goals positivity
  have K : k ≤ n := by
    simp only [log_pow, Nat.cast_add, Nat.cast_one] at h₂
    have := A.trans_lt h₂
    have' := lt_of_mul_lt_mul_right this <| by positivity
    norm_cast at this
    rw [Nat.lt_succ] at this
    exact this
  let N : ℕ := n+1
  have hN : k + 1 ≤ N ∧ Λ * (b-a) / 2 ^ N < 10 * δ ∧ 2 ^ N ≤ Λ * (b - a) / (5 * δ) := by
    dsimp [N]
    constructor
    · gcongr
    constructor
    · rw [div_lt_iff] at J ⊢
      · convert J using 1
        ring
      all_goals positivity
    · rw [le_div_iff] at I ⊢
      · convert I using 1
        ring
      all_goals positivity
  have : k ≤ N := by linarith only [hN.1] -- removed `(2:ℝ) ^ k ≠ 0`, use `positivity`
  have hNk₁ : 2 ^ (N - k) * 2 ^ k = 2 ^ N := by
    rw [← pow_add]
    congr! 1
    apply Nat.sub_add_cancel this
  have hNk₂ : (2:ℝ) ^ (N - k) = 2 ^ N / 2 ^ k := by
    field_simp
    exact_mod_cast hNk₁

  /- Define `2 ^ N` points along the path, separated by at most `10 * δ`, and their projections. -/
  let g : ℕ → X := fun i ↦ f (a + (b-a) * i / 2^N)
  have hg_endpoints : g 0 = f a ∧ g (2^N) = f b := by simp [g]
  have A (i : ℕ) (hi : i < (2 ^ N)) : dist (g i) (g (i + 1)) ≤ 10 * δ + C := by
    calc dist (g i) (g (i + 1))
        ≤ Λ * |(a + (b-a) * i / 2^N) - (a + (b-a) * (i + 1) / 2^N)| + C := by
          dsimp only [g]
          convert h _ _ (hi_mem hi.le) (hi_mem hi)
          norm_cast
      _ = Λ * (b-a) / 2^N + C := by
          rw [mul_div_assoc Λ]
          congr
          calc _ = |- ((b - a) / 2 ^ N)| := by
                congr
                field_simp
                ring
            _ = _ := by
                rw [abs_neg, abs_of_nonneg]
                positivity
      _ ≤ 10 * δ + C := by gcongr; exact hN.2.1.le
  let p : ℕ → X := fun i ↦ if i = 0 then pa else if i = 2^N then pb else (hG_nonempty (g i)).choose
  have B (i : ℕ) (_ : i ≤ (2 ^ N)) : p i ∈ proj_set (g i) G := by
    dsimp only [p]
    split_ifs with hi' hi'
    · rw [hi', hg_endpoints.1]
      exact hpa
    · rw [hi', hg_endpoints.2]
      exact hpb
    · exact (hG_nonempty _).choose_spec
  have C (i : ℕ) (hi : i ≤ (2 ^ N)) : dist (p i) (g i) ≥ 5 * δ * k + 15/2 * δ + C/2 := by
    calc 5 * δ * k + 15/2 * δ + C/2 ≤ D := hk'.1
      _ ≤ infDist (g i) G := hG' _ <| hi_mem hi
      _ = dist (p i) (g i) := by rw [dist_comm, (B i hi).2]
  /- Use the basic statement to show that, along packets of size `2 ^ k`, the projections
  are within `5 * δ` of each other. -/
  have I (j : ℕ) (hj : j < (2 ^ (N - k))) : dist (p (2^k * j)) (p (2^k * (j + 1))) ≤ 5 * δ := by
    have I (i : ℕ) (hi : i ≤ (2 ^ k)) : i + 2^k * j ≤ (2^N) := by
      calc i + 2 ^ k * j ≤ 2^k + 2^k * (2^(N-k)-1) := by
            gcongr
            omega
        _ = 2^N := by
            rw [← hNk₁]
            clear_value N
            have : 2 ^ (N - k) ≥ 1 := Nat.one_le_pow _ _ <| by norm_num
            zify [this]
            ring
    have I' (i : ℕ) (hi : i < (2 ^ k)) : i + 2^k * j < (2^N) := by
      calc i + 2 ^ k * j < 2^k + 2 ^ k * j := by gcongr
        _ ≤ 2 ^ k + 2^k * (2^(N-k)-1) := by
            gcongr
            omega
        _ = 2^N := by
            rw [← hNk₁]
            clear_value N
            have : 2 ^ (N - k) ≥ 1 := Nat.one_le_pow _ _ <| by norm_num
            zify [this]
            ring
    let g' : ℕ → X := fun i ↦ g (i + 2^k * j)
    let p' : ℕ → X := fun i ↦ p (i + 2^k * j)
    calc dist (p (2 ^ k * j)) (p (2 ^ k * (j + 1)))
          = dist (p' 0) (p' (2^k)) := by congr <;> ring
        _ ≤ 5 * deltaG X := by
            apply Main (g := g') _ _ _ (fun i hi ↦ B _ ?_) (fun i hi ↦ C _ ?_) (fun i hi ↦ ?_) hC
            · apply I _ hi
            · apply I _ hi
            · dsimp [g']
              convert A (i + 2 ^ k * j) ?_ using 3
              · ring
              apply I' _ hi
        _ ≤ 5 * δ := by gcongr
  /- Control the total distance by adding the contributions of blocks of size `2 ^ k`. -/
  have (j : ℕ) : dist (p 0) (p (2^k * j))
      ≤ (∑ i in Finset.range j, dist (p (2^k * i)) (p (2^k * (i + 1)))) := by
    induction' j with j hj
    · simp
    calc dist (p 0) (p (2^k * (j + 1)))
        ≤ dist (p 0) (p (2^k * j)) + dist (p (2^k * j)) (p (2^k * (j + 1))) := dist_triangle ..
      _ ≤ (∑ i in Finset.range j, dist (p (2^k * i)) (p (2^k * (i + 1))))
            + dist (p (2^k * j)) (p (2^k * (j + 1))) := by gcongr
      _ = (∑ i in Finset.range (j + 1), dist (p (2^k * i)) (p (2^k * (i + 1)))) := by
          rw [Finset.sum_range_succ]
  clear C
  calc dist pa pb = dist (p 0) (p (2^N)) := by simp [p]
    _ = dist (p 0) (p (2^k * 2^(N-k))) := by
        rw [← hNk₁]
        ring_nf
    _ ≤ (∑ i in Finset.range (2^(N-k)), dist (p (2^k * i)) (p (2^k * (i + 1)))) := this _
    _ ≤ (∑ i in Finset.range (2^(N-k)), 5 * δ) := by
        gcongr with i hi
        apply I
        simpa using hi
    _ = 5 * δ * 2^(N-k) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        ring
    _ = 5 * δ * 2^N * (1/ 2^k) := by rw [hNk₂]; ring
    _ ≤ 5 * δ * (2 * Λ * (b-a)/(10 * δ)) * (2 * exp (15/2/5 * log 2) * exp (- ((D-C/2) * log 2 / (5 * δ)))) := by
        gcongr
        convert hN.2.2 using 1
        field_simp
        ring
    _ = (2 * exp (15/2/5 * log 2)) * Λ * (b-a) * exp (-(D-C/2) * log 2 / (5 * δ)) := by
        field_simp
        ring_nf
    _ = _ := by
        congrm ?_ * Λ * _ * _
        calc _ = 2 * (exp (log 2) * exp (1 / 2 * log 2)) := by
              rw [← exp_add]
              congrm 2 * exp ?_
              ring
          _ = _ := by
              rw [exp_log]
              · ring
              positivity
    _ ≤  _ := le_max_right _ _

/-- We deduce from the previous result that a projection on a quasiconvex set is also
exponentially contracting. To do this, one uses the contraction of a projection on a geodesic, and
one adds up the additional errors due to the quasi-convexity. In particular, the projections on the
original quasiconvex set or the geodesic do not have to coincide, but they are within distance at
most `C + 8 * δ`. -/
-- **Lemma 2.5**
lemma quasiconvex_projection_exp_contracting {K : ℝ}
    (hKG : quasiconvex K G) {f : ℝ → X} {a b Λ C : ℝ}
    (h : ∀ x y, x ∈ Icc a b → y ∈ Icc a b → dist (f x) (f y) ≤ Λ * |x - y| + C) -- NB changed from `dist x y` in original
    (hab : a ≤ b) {pa : X} (hpaG : pa ∈ proj_set (f a) G) {pb : X} (hpbG : pb ∈ proj_set (f b) G)
    {D : ℝ} (hG : ∀ t, t ∈ Icc a b → infDist (f t) G ≥ D)
    {δ : ℝ} (hD : D ≥ 15/2 * δ + K + C/2)
    (hδ : δ > deltaG X) (hC : C ≥ 0) (hΛ : Λ ≥ 0) :
    dist pa pb ≤ 2 * K + 8 * δ
      + max (5 * deltaG X)
          ((4 * exp (1/2 * log 2)) * Λ * (b-a) * exp (-(D - K - C/2) * log 2 / (5 * δ))) := by
  obtain ⟨H, hH₁, hH₂⟩ : ∃ H, geodesic_segment_between H pa pb ∧ ∀ q, q ∈ H → infDist q G ≤ K :=
    hKG.2 hpaG.1 hpbG.1
  obtain ⟨qa, hqa⟩ : ∃ qa, qa ∈ proj_set (f a) H := by
    apply proj_set_nonempty_of_compact
    · apply (geodesic_segment_topology ⟨_, _, hH₁⟩).1
    · apply (geodesic_segment_topology ⟨_, _, hH₁⟩).2.2.2.2.2
  obtain ⟨qb, hqb⟩ : ∃ qb, qb ∈ proj_set (f b) H := by
    apply proj_set_nonempty_of_compact
    · apply (geodesic_segment_topology ⟨_, _, hH₁⟩).1
    · apply (geodesic_segment_topology ⟨_, _, hH₁⟩).2.2.2.2.2
  have hG_nonempty : G.Nonempty := ⟨_, hpaG.1⟩
  have I (t : ℝ) (ht : t ∈ Icc a b) : infDist (f t) H ≥ D - K := by
    have : Nonempty H := by simpa only [nonempty_subtype] using (geodesic_segment_endpoints hH₁).2.2
    rw [infDist_eq_iInf, ge_iff_le, le_ciInf_iff]
    · rintro ⟨h, h_mem_H⟩
      dsimp
      suffices D - dist (f t) h ≤ K by linarith only [this]
      apply le_of_forall_le_of_dense
      intro x hx
      have := hH₂ h h_mem_H |>.trans_lt hx
      rw [infDist_lt_iff hG_nonempty] at this
      obtain ⟨g, hgG, hgha⟩ := this
      have :=
      calc D ≤ dist (f t) g := by
            apply (hG _ ht).trans
            apply infDist_le_dist_of_mem hgG
        _ ≤ dist (f t) h + dist h g := dist_triangle ..
      linarith only [this, hgha]
    · refine ⟨0, ?_⟩
      simp only [lowerBounds, mem_range, Subtype.exists, exists_prop, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, mem_setOf_eq]
      intros
      positivity

  have Q : dist qa qb ≤ max (5 * deltaG X) ((4 * exp (1/2 * log 2))
          * Λ * (b-a) * exp (-((D - K)-C/2 ) * log 2 / (5 * δ))) := by
    refine geodesic_projection_exp_contracting ⟨_, _, hH₁⟩ h hab hqa hqb I ?_ hδ hC hΛ
    linarith only [hD]

  have A : dist pa qa ≤ 4 * δ + K := by
    suffices dist pa qa - 4 * δ ≤ K by linarith only [this]
    apply le_of_forall_le_of_dense
    intro x hx
    obtain ⟨g, hgG, hgha⟩ : ∃ y ∈ G, dist qa y < x := by
      have := hH₂ qa hqa.1 |>.trans_lt hx
      rwa [← infDist_lt_iff hG_nonempty]
    have h₁ :=
    calc dist (f a) pa ≤ dist (f a) g := proj_set_dist_le hgG hpaG
      _ ≤ dist (f a) qa + dist qa g := dist_triangle ..
    have h₂ := dist_along_geodesic ⟨_, _, hH₁⟩ hqa (geodesic_segment_endpoints hH₁).1
    rw [dist_comm pa]
    linarith only [h₁, h₂, hgha, hδ]

  have B : dist qb pb ≤ 4 * δ + K := by
    suffices dist qb pb - 4 * δ ≤ K by linarith only [this]
    apply le_of_forall_le_of_dense
    intro x hx
    obtain ⟨g, hgG, hghb⟩ : ∃ y ∈ G, dist qb y < x := by
      have := hH₂ qb hqb.1 |>.trans_lt hx
      rwa [← infDist_lt_iff hG_nonempty]
    have h₁ :=
    calc dist (f b) pb ≤ dist (f b) g := proj_set_dist_le hgG hpbG
      _ ≤ dist (f b) qb + dist qb g := dist_triangle ..
    have h₂ := dist_along_geodesic ⟨_, _, hH₁⟩ hqb (geodesic_segment_endpoints hH₁).2.1
    linarith only [h₁, h₂, hghb, hδ]

  have : dist pa pb ≤ dist pa qa + dist qa qb + dist qb pb := dist_triangle4 ..
  linarith only [A, B, Q, this]
