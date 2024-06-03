/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD -/
import GromovHyperbolicity.Quasiconvex
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Set Metric Real Classical

/-! The main result of this file is `quasiconvex_projection_exp_contracting`, a key technical result
used in the Gouëzel-Shchur quantitative Morose lemma. -/

variable {X : Type*} [MetricSpace X] [Gromov_hyperbolic_space X] [GeodesicSpace X]

open Gromov_hyperbolic_space

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
    (hpxG : px ∈ proj_set x G) (hpyG : py ∈ proj_set y G) {δ C M : ℝ}
    (hδ : δ ≥ deltaG X) {M : ℝ} (hxy : dist x y ≤ 10 * δ + C)
    (hM : M ≥ 15/2 * δ) (hpx : dist px x ≥ M + 5 * δ + C/2) (hpy : dist py y ≥ M + 5 * δ + C/2)
    (hC : C ≥ 0) :
    dist (geodesic_segment_param {px‒x} px M) (geodesic_segment_param {py‒y} py M) ≤ 5 * δ := by
  have hpxpyx : dist px x ≤ dist py x := sorry
--     using proj_setD(2)[OF assms(2)] infDist_le[OF proj_setD(1)[OF assms(3)], of x] by (simp add: metric_space_class.dist_commute)
  have hpypxy : dist py y ≤ dist px y := sorry
--     using proj_setD(2)[OF assms(3)] infDist_le[OF proj_setD(1)[OF assms(2)], of y] by (simp add: metric_space_class.dist_commute)
  have hδ₀ : 0 ≤ δ := by
    have : Inhabited X := ⟨x⟩
    linarith only [hδ, delta_nonneg X]
  have hM' : 0 ≤ M ∧ M ≤ dist px x ∧ M ≤ dist px y ∧ M ≤ dist py x ∧ M ≤ dist py y := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have : px ∈ G ∧ py ∈ G := ⟨proj_setD hpxG, proj_setD hpyG⟩
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
  have : px ∈ proj_set x' G := sorry
--     by (rule proj_set_geodesic_same_basepoint[OF \<open>px ∈ proj_set x G\<close> _ *], auto)
  have hpxx'M : dist px x' = M := by
    apply geodesic_segment_param_in_geodesic_spaces6
    exact ⟨hM'.1, hM'.2.1⟩
  have hpxpyx' : dist px x' ≤ dist py x' := sorry
--     using proj_setD(2)[OF \<open>px ∈ proj_set x' G\<close>] infDist_le[OF proj_setD(1)[OF assms(3)], of x'] by (simp add: metric_space_class.dist_commute)
  have : dist px x = dist px x' + dist x' x := by
    rw [← geodesic_segment_dist (some_geodesic_is_geodesic_segment px x).1 hx'_mem]
  have Ixx : Gromov_product_at px x' x = M := by
    dsimp only [Gromov_product_at]
    linarith only [this, hpxx'M]
  have Iyx : Gromov_product_at py x x' ≥ M := by
    simp only [Gromov_product_at, dist_comm] at Ixx hpxpyx hpxpyx' ⊢
    linarith only [Ixx, hpxpyx, hpxpyx']
  have hy'_mem : y' ∈ {py‒y} := geodesic_segment_param_in_segment (some_geodesic_endpoints).2.2
  have : py ∈ proj_set y' G := sorry
--     by (rule proj_set_geodesic_same_basepoint[OF \<open>py ∈ proj_set y G\<close> _ *], auto)
  have hpyy'M : dist py y' = M := by
    apply geodesic_segment_param_in_geodesic_spaces6
    exact ⟨hM'.1, hM'.2.2.2.2⟩
  have hpypyy' : dist py y' ≤ dist px y' := sorry
--     using proj_setD(2)[OF \<open>py ∈ proj_set y' G\<close>] infDist_le[OF proj_setD(1)[OF assms(2)], of y'] by (simp add: metric_space_class.dist_commute)
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
lemma geodesic_projection_exp_contracting (hG : geodesic_segment G) {f : ℝ → X} {a b : ℝ}
    (h : ∀ x y, x ∈ Icc a b → y ∈ Icc a b → dist (f x) (f y) ≤ Λ * |x - y| + C) -- NB changed from `dist x y` in original
    (hab : a ≤ b) (hpa : pa ∈ proj_set (f a) G) (hpb : pb ∈ proj_set (f b) G)
    (hG' : ∀ t, t ∈ Icc a b → infDist (f t) G ≥ D) (hD : D ≥ 15/2 * δ + C/2)
    (hδ : δ > deltaG X) (hC : C ≥ 0) (hΛ : Λ ≥ 0) :
    dist pa pb ≤ max (5 * deltaG X)
      ((4 * exp (1/2 * log 2)) * Λ * (b-a) * exp (-(D-C/2) * log 2 / (5 * δ))) := by
  have : Inhabited X := ⟨pa⟩
  have : δ > 0 := by
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
              (∀ i ∈ Icc 0 (2^k), p i ∈ proj_set (g i) G)
            → (∀ i ∈ Icc 0 (2^k), dist (p i) (g i) ≥ 5 * δ * k + 15/2 * δ + c/2)
            → (∀ i ∈ Ico 0 (2^k), dist (g i) (g (i + 1)) ≤ 10 * δ + c)
            → c ≥ 0
            → dist (p 0) (p (2^k)) ≤ 5 * deltaG X := by
    sorry
--   have Main: "∀ c g p. (∀ i ∈ {0..2^k}. p i ∈ proj_set (g i) G)
--             → (∀ i ∈ {0..2^k}. dist (p i) (g i) ≥ 5 * δ * k + 15/2 * δ + c/2)
--             → (∀ i ∈ {0..<2^k}. dist (g i) (g (Suc i)) ≤ 10 * δ + c)
--             → c ≥ 0
--             → dist (p 0) (p (2^k)) ≤ 5 * deltaG X" for k
--   proof (induction k)
--     case 0
--     then have H: "p 0 ∈ proj_set (g 0) G"
--                  "p 1 ∈ proj_set (g 1) G"
--                  "dist (g 0) (g 1) ≤ 10 * δ + c"
--                  "dist (p 0) (g 0) ≥ 15/2 * δ + c/2"
--                  "dist (p 1) (g 1) ≥ 15/2 * δ + c/2"
--       by auto
--     have := calc dist (p 0) (p 1) ≤ max (5 * deltaG X) (dist (g 0) (g 1) - dist (p 0) (g 0) - dist (p 1) (g 1) + 10 * deltaG X)"
--       by (rule proj_along_geodesic_contraction[OF \<open>geodesic_segment G\<close> \<open>p 0 ∈ proj_set (g 0) G\<close> \<open>p 1 ∈ proj_set (g 1) G\<close>])
--     _ ≤ max (5 * deltaG X) (5 * deltaG X)"
--       apply (intro mono_intros) using H \<open>delta > deltaG X\<close> by auto
--     finally show "dist (p 0) (p (2^0)) ≤ 5 * deltaG X"
--       by auto
--   next
--     case (Suc k)
--     have *: "5 * δ * real (k + 1) + 5 * δ = 5 * δ * real (Suc k + 1)"
--       by (simp add: algebra_simps)
--     define h where "h = (\<lambda>i. geodesic_segment_param {p i‒g i} (p i) (5 * δ * k + 15/2 * δ))"
--     have h_dist: "dist (h i) (h (Suc i)) ≤ 5 * δ" if "i ∈ {0..<2^(Suc k)}" for i
--       unfolding h_def apply (rule geodesic_projection_exp_contracting_aux[OF \<open>geodesic_segment G\<close> _ _ less_imp_le[OF \<open>delta > deltaG X\<close>]])
--       unfolding * using Suc.prems that \<open>delta > 0\<close> by (auto simp add: algebra_simps divide_simps)
--     define g' where "g' = (\<lambda>i. h (2 * i))"
--     define p' where "p' = (\<lambda>i. p (2 * i))"
--     have "dist (p' 0) (p' (2^k)) ≤ 5 * deltaG X"
--     proof (rule Suc.IH[where ?g = g' and ?c = 0])
--       show "∀ i∈{0..2 ^ k}. p' i ∈ proj_set (g' i) G"
--       proof
--         fix i::nat assume "i ∈ {0..2^k}"
--         then have *: "2 * i ∈ {0..2^(Suc k)}" by auto
--         show "p' i ∈ proj_set (g' i) G"
--           unfolding p'_def g'_def h_def apply (rule proj_set_geodesic_same_basepoint[of _ "g (2 * i)" _ "{p(2 * i)‒g(2 * i)}"])
--           using Suc * by (auto simp add: geodesic_segment_param_in_segment)
--       qed
--       show "∀ i∈{0..2 ^ k}. 5 * δ * k + 15/2 * δ + 0/2 ≤ dist (p' i) (g' i)"
--       proof
--         fix i::nat assume "i ∈ {0..2^k}"
--         then have *: "2 * i ∈ {0..2^(Suc k)}" by auto
--         have "5 * δ * k + 15/2 * δ ≤ 5 * δ * Suc k + 15/2 * δ + c/2"
--           using \<open>delta > 0\<close> \<open>c ≥ 0\<close> by (auto simp add: algebra_simps divide_simps)
--         _ ≤ dist (p (2 * i)) (g (2 * i))"
--           using Suc * by auto
--         finally have *: "5 * δ * k + 15/2 * δ ≤ dist (p (2 * i)) (g (2 * i))" by simp
--         have "dist (p' i) (g' i) = 5 * δ * k + 15/2 * δ"
--           unfolding p'_def g'_def h_def apply (rule geodesic_segment_param_in_geodesic_spaces(6))
--           using * \<open>delta > 0\<close> by auto
--         then show "5 * δ * k + 15/2 * δ + 0/2 ≤ dist (p' i) (g' i)" by simp
--       qed
--       show "∀ i∈{0..<2 ^ k}. dist (g' i) (g' (Suc i)) ≤ 10 * δ + 0"
--       proof
--         fix i::nat assume *: "i ∈ {0..<2 ^ k}"
--         have := calc dist (g' i) (g' (Suc i)) = dist (h (2 * i)) (h (Suc (Suc (2 * i))))"
--           unfolding g'_def by auto
--         _ ≤ dist (h (2 * i)) (h (Suc (2 * i))) + dist (h (Suc (2 * i))) (h (Suc (Suc (2 * i))))"
--           by (intro mono_intros)
--         _ ≤ 5 * δ + 5 * δ"
--           apply (intro mono_intros h_dist) using * by auto
--         finally show "dist (g' i) (g' (Suc i)) ≤ 10 * δ + 0" by simp
--       qed
--     qed (simp)
--     then show "dist (p 0) (p (2 ^ Suc k)) ≤ 5 * deltaG X"
--       unfolding p'_def by auto
--   qed

  /- Now, we will apply the previous basic statement to points along our original path. We
  introduce `k`, the number of steps for which the pushing process can be done -- it only depends on
  the original distance `D` to `G`. -/

  let k : ℕ := Nat.floor ((D - C/2 - 15/2 * δ) / (5 * δ))
--   have "int k = floor((D - C/2 - 15/2 * δ)/(5 * δ))"
--     unfolding k_def apply (rule nat_0_le) using \<open>D ≥ 15/2 * δ + C/2\<close> \<open>delta > 0\<close> by auto
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

  by_cases h_split : Λ * (b-a) ≤ 10 * δ * 2^k
  · /- First, treat the case where the path is rather short. -/
    let g : ℕ → X := fun i ↦ f (a + (b-a) * i/2^k)
    have hg_endpoints : g 0 = f a ∧ g (2^k) = f b := by simp [g]
    -- TODO make `i ∈ Icc 0 (2 ^ k)` just `i ≤ 2 ^ k`?
    have (i : ℕ) (hi : i ∈ Icc 0 (2 ^ k)) : a + (b-a) * i/2^k ∈ Icc a b := by
      dsimp [Icc] at hi ⊢
      simp only [zero_le, true_and] at hi
      constructor
      · have : 0 ≤ (b - a) * i / 2 ^ k := by positivity
        linarith only [this]
      · calc a + (b - a) * i / 2 ^ k ≤ a + (b - a) * 2 ^ k / 2 ^ k := by gcongr; exact_mod_cast hi
          _ = b := by field_simp
    have A (i : ℕ) (hi : i ∈ Ico 0 (2 ^ k)) : dist (g i) (g (i + 1)) ≤ 10 * δ + C := by
      calc dist (g i) (g (i + 1)) ≤ Λ * |(a + (b-a) * i/2^k) - (a + (b-a) * (i + 1)/2^k)| + C := by
            dsimp [g]
            convert h (a + (b - a) * i / 2 ^ k) (a + (b - a) * ↑(i + 1) / 2 ^ k) ?_ ?_
            · norm_cast
            · apply this
              exact Ico_subset_Icc_self hi
            · apply this
              refine ⟨?_, hi.2⟩
              positivity
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
    have hG_nonempty (x : X) : (proj_set x G).Nonempty := sorry
--         apply (rule proj_set_nonempty_of_proper) using geodesic_segment_topology[OF \<open>geodesic_segment G\<close>] by auto
    let p := fun i ↦ if i = 0 then pa else if i = 2^k then pb else (hG_nonempty  (g i)).choose
    have B (i : ℕ) (hi : i ∈ Icc 0 (2 ^ k)) : p i ∈ proj_set (g i) G := by
      dsimp only [p]
      split_ifs with hi' hi'
      · rw [hi', hg_endpoints.1]
        exact hpa
      · rw [hi', hg_endpoints.2]
        exact hpb
      · exact (hG_nonempty _).choose_spec
    have C (i : ℕ) (hi : i ∈ Icc 0 (2 ^ k)) : dist (p i) (g i) ≥ 5 * δ * k + 15/2 * δ + C/2 := by
      calc 5 * δ * k + 15/2 * δ + C/2 ≤ D := hk'.1
        _ ≤ infDist (g i) G := hG' _ <| this _ hi
        _ = dist (p i) (g i) := sorry
--         using that proj_setD(2)[OF B[OF that]] by (simp add: metric_space_class.dist_commute)
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
--     ultimately have A: "log 2 (lambda * (b-a)/(10 * δ)) ≥ k" by auto
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
  have : (2:ℝ) ^ (N - k) = 2 ^ N / 2 ^ k := by
    field_simp
    rw [← pow_add]
    congr! 1
    apply Nat.sub_add_cancel this
  sorry

--     text \<open>Define $2^N$ points along the path, separated by at most $10δ$, and their projections.\<close>
--     define g::"nat → 'a" where "g = (\<lambda>i. f(a + (b-a) * i/2^N))"
--     have "g 0 = f a" "g(2^N) = f b"
--       unfolding g_def by auto
--     have *: "a + (b-a) * i/2^N ∈ Icc a b" if "i ∈ {0..2^N}" for i::nat
--     proof -
--       have "a + (b - a) * (real i / 2 ^ N) ≤ a + (b-a) * (2^N/2^N)"
--         apply (intro mono_intros) using that \<open>a ≤ b\<close> by auto
--       then show ?thesis using \<open>a ≤ b\<close> by auto
--     qed
--     have A: "dist (g i) (g (Suc i)) ≤ 10 * δ + C" if "i ∈ {0..<2^N}" for i
--     proof -
--       have := calc dist (g i) (g (Suc i)) ≤ lambda * dist (a + (b-a) * i/2^N) (a + (b-a) * (Suc i)/2^N) + C"
--         unfolding g_def apply (intro assms(2) *)
--         using that by auto
--       _ = lambda * (b-a)/2^N + C"
--         unfolding dist_real_def using \<open>a ≤ b\<close> by (auto simp add: algebra_simps divide_simps)
--       _ ≤ 10 * δ + C"
--         using N by simp
--       finally show ?thesis by simp
--     qed
--     define p where "p = (\<lambda>i. if i = 0 then pa else if i = 2^N then pb else SOME p. p ∈ proj_set (g i) G)"
--     have B: "p i ∈ proj_set (g i) G" if "i ∈ {0..2^N}" for i
--     proof (cases "i = 0 \<or> i = 2^N")
--       case True
--       then show ?thesis
--         using \<open>pa ∈ proj_set (f a) G\<close> \<open>pb ∈ proj_set (f b) G\<close> unfolding p_def g_def by auto
--     next
--       case False
--       then have "p i = (SOME p. p ∈ proj_set (g i) G)"
--         unfolding p_def by auto
--       moreover have "proj_set (g i) G \<noteq> {}"
--         apply (rule proj_set_nonempty_of_proper) using geodesic_segment_topology[OF \<open>geodesic_segment G\<close>] by auto
--       ultimately show ?thesis
--         using some_in_eq by auto
--     qed
--     have C: "dist (p i) (g i) ≥ 5 * δ * k + 15/2 * δ + C/2" if "i ∈ {0..2^N}" for i
--     proof -
--       have := calc 5 * δ * k + 15/2 * δ + C/2 ≤ D"
--         using k(1) by simp
--       _ ≤ infDist (g i) G"
--         unfolding g_def apply (rule \<open>∀ t. t ∈ Icc a b → infDist (f t) G ≥ D\<close>) using * that by auto
--       _ = dist (p i) (g i)"
--         using that proj_setD(2)[OF B[OF that]] by (simp add: metric_space_class.dist_commute)
--       finally show ?thesis by simp
--     qed
--     text \<open>Use the basic statement to show that, along packets of size $2^k$, the projections
--     are within $5δ$ of each other.\<close>
--     have I: "dist (p (2^k * j)) (p (2^k * (Suc j))) ≤ 5 * δ" if "j ∈ {0..<2^(N-k)}" for j
--     proof -
--       have I: "i + 2^k * j ∈ {0..2^N}" if "i ∈ {0..2^k}" for i
--       proof -
--         have := calc i + 2 ^ k * j ≤ 2^k + 2^k * (2^(N-k)-1)"
--           apply (intro mono_intros) using that \<open>j ∈ {0..<2^(N-k)}\<close> by auto
--         _ = 2^N"
--           using \<open>k +1 ≤ N\<close> by (auto simp add: algebra_simps semiring_normalization_rules(26))
--         finally show ?thesis by auto
--       qed
--       have I': "i + 2^k * j ∈ {0..<2^N}" if "i ∈ {0..<2^k}" for i
--       proof -
--         have := calc i + 2 ^ k * j < 2^k + 2^k * (2^(N-k)-1)"
--           apply (intro mono_intros) using that \<open>j ∈ {0..<2^(N-k)}\<close> by auto
--         _ = 2^N"
--           using \<open>k +1 ≤ N\<close> by (auto simp add: algebra_simps semiring_normalization_rules(26))
--         finally show ?thesis by auto
--       qed
--       define g' where "g' = (\<lambda>i. g (i + 2^k * j))"
--       define p' where "p' = (\<lambda>i. p (i + 2^k * j))"
--       have := calc dist (p' 0) (p' (2^k)) ≤ 5 * deltaG X"
--         apply (rule Main[where ?g = g' and ?c = C]) unfolding p'_def g'_def using A B C I I' \<open>C ≥ 0\<close> by auto
--       _ ≤ 5 * δ"
--         using \<open>deltaG X < δ\<close> by auto
--       finally show ?thesis
--         unfolding p'_def by auto
--     qed
--     text \<open>Control the total distance by adding the contributions of blocks of size $2^k$.\<close>
--     have *: "dist (p 0) (p(2^k * j)) ≤ (\<Sum>i<j. dist (p (2^k * i)) (p (2^k * (Suc i))))" for j
--     proof (induction j)
--       case (Suc j)
--       have := calc dist (p 0) (p(2^k * (Suc j))) ≤ dist (p 0) (p(2^k * j)) + dist (p(2^k * j)) (p(2^k * (Suc j)))"
--         by (intro mono_intros)
--       _ ≤ (\<Sum>i<j. dist (p (2^k * i)) (p (2^k * (Suc i)))) + dist (p(2^k * j)) (p(2^k * (Suc j)))"
--         using Suc.IH by auto
--       _ = (\<Sum>i<Suc j. dist (p (2^k * i)) (p (2^k * (Suc i))))"
--         by auto
--       finally show ?case by simp
--     qed (auto)
--     have := calc dist pa pb = dist (p 0) (p (2^N))"
--       unfolding p_def by auto
--     _ = dist (p 0) (p (2^k * 2^(N-k)))"
--       using \<open>k +1 ≤ N\<close> by (auto simp add: semiring_normalization_rules(26))
--     _ ≤ (\<Sum>i<2^(N-k). dist (p (2^k * i)) (p (2^k * (Suc i))))"
--       using * by auto
--     _ ≤ (\<Sum>(i::nat)<2^(N-k). 5 * δ)"
--       apply (rule sum_mono) using I by auto
--     _ = 5 * δ * 2^(N-k)"
--       by auto
--     _ = 5 * δ * 2^N * (1/ 2^k)"
--       unfolding \<open>(2^(N-k)::real) = 2^N/2^k\<close> by simp
--     _ ≤ 5 * δ * (2 * lambda * (b-a)/(10 * δ)) * (2 * exp(15/2/5 * log 2) * exp(- ((D-C/2) * log 2 / (5 * δ))))"
--       apply (intro mono_intros) using \<open>delta > 0\<close> \<open>lambda > 0\<close> \<open>a < b\<close> hk N by auto
--     _ = (2 * exp(15/2/5 * log 2)) * lambda * (b-a) * exp(-(D-C/2) * log 2 / (5 * δ))"
--       using \<open>delta > 0\<close> by (auto simp add: algebra_simps divide_simps)
--     finally show ?thesis
--       unfolding \<open>exp(15/2/5 * log 2) = 2 * exp(1/2 * ln (2::real))\<close> by auto
--   qed
-- qed

/-- We deduce from the previous result that a projection on a quasiconvex set is also
exponentially contracting. To do this, one uses the contraction of a projection on a geodesic, and
one adds up the additional errors due to the quasi-convexity. In particular, the projections on the
original quasiconvex set or the geodesic do not have to coincide, but they are within distance at
most $C + 8 δ$. -/
-- **Lemma 2.5**
-- (in Gromov_hyperbolic_space_geodesic)
lemma quasiconvex_projection_exp_contracting
    (hKG : quasiconvex K G) {f : ℝ → X}
    (h : ∀ x y, x ∈ Icc a b → y ∈ Icc a b → dist (f x) (f y) ≤ Λ * dist x y + C)
    (hab : a ≤ b) (hpaG : pa ∈ proj_set (f a) G) (hpbG : pb ∈ proj_set (f b) G)
    (hG : ∀ t, t ∈ Icc a b → infDist (f t) G ≥ D)
    (hD : D ≥ 15/2 * δ + K + C/2)
    (hδ : δ > deltaG X) (hC : C ≥ 0) (hΛ : Λ ≥ 0) :
    dist pa pb ≤ 2 * K + 8 * δ
      + max (5 * deltaG X)
          ((4 * exp (1/2 * log 2)) * Λ * (b-a) * exp (-(D - K - C/2) * log 2 / (5 * δ))) := by
  sorry
-- proof -
--   obtain H where H: "geodesic_segment_between H pa pb" "∀ q. q ∈ H → infDist q G ≤ K"
--     using quasiconvexD[OF assms(1) proj_setD(1)[OF \<open>pa ∈ proj_set (f a) G\<close>] proj_setD(1)[OF \<open>pb ∈ proj_set (f b) G\<close>]] by auto
--   obtain qa where qa: "qa ∈ proj_set (f a) H"
--     using proj_set_nonempty_of_proper[of H "f a"] geodesic_segment_topology[OF geodesic_segmentI[OF H(1)]] by auto
--   obtain qb where qb: "qb ∈ proj_set (f b) H"
--     using proj_set_nonempty_of_proper[of H "f b"] geodesic_segment_topology[OF geodesic_segmentI[OF H(1)]] by auto

--   have I: "infDist (f t) H ≥ D - K" if "t ∈ Icc a b" for t
--   proof -
--     have *: "D - K ≤ dist (f t) h" if "h ∈ H" for h
--     proof -
--       have "D - K - dist (f t) h ≤ e" if "e > 0" for e
--       proof -
--         have *: "infDist h G < K + e" using H(2)[OF \<open>h ∈ H\<close>] \<open>e > 0\<close> by auto
--         obtain g where g: "g ∈ G" "dist h g < K + e"
--           using infDist_almost_attained[OF *] proj_setD(1)[OF \<open>pa ∈ proj_set (f a) G\<close>] by auto
--         have := calc D ≤ dist (f t) g"
--           using \<open>∀ t. t ∈ Icc a b → infDist (f t) G ≥ D\<close>[OF \<open>t ∈ Icc a b\<close>] infDist_le[OF \<open>g ∈ G\<close>, of "f t"] by auto
--         _ ≤ dist (f t) h + dist h g"
--           by (intro mono_intros)
--         _ ≤ dist (f t) h + K + e"
--           using g(2) by auto
--         finally show ?thesis by auto
--       qed
--       then have *: "D - K - dist (f t) h ≤ 0"
--         using dense_ge by blast
--       then show ?thesis by simp
--     qed
--     have "D - K ≤ Inf (dist (f t) ` H)"
--       apply (rule cInf_greatest) using * H(1) by auto
--     then show "D - K ≤ infDist (f t) H"
--       apply (subst infDist_notempty) using H(1) by auto
--   qed
--   have Q: "dist qa qb ≤ max (5 * deltaG X) ((4 * exp(1/2 * log 2)) * lambda * (b-a) * exp(-((D - K)-C/2 ) * log 2 / (5 * delta)))"
--     apply (rule geodesic_projection_exp_contracting[OF geodesic_segmentI[OF \<open>geodesic_segment_between H pa pb\<close>] assms(2) assms(3)])
--     using qa qb I assms by auto

--   have A: "dist pa qa ≤ 4 * delta + K"
--   proof -
--     have "dist (f a) pa - dist (f a) qa - K ≤ e" if "e > 0" for e::real
--     proof -
--       have *: "infDist qa G < K + e" using H(2)[OF proj_setD(1)[OF qa]] \<open>e > 0\<close> by auto
--       obtain g where g: "g ∈ G" "dist qa g < K + e"
--         using infDist_almost_attained[OF *] proj_setD(1)[OF \<open>pa ∈ proj_set (f a) G\<close>] by auto
--       have := calc dist (f a) pa ≤ dist (f a) g"
--         unfolding proj_setD(2)[OF \<open>pa ∈ proj_set (f a) G\<close>] using infDist_le[OF \<open>g ∈ G\<close>, of "f a"] by simp
--       _ ≤ dist (f a) qa + dist qa g"
--         by (intro mono_intros)
--       _ ≤ dist (f a) qa + K + e"
--         using g(2) by auto
--       finally show ?thesis by simp
--     qed
--     then have I: "dist (f a) pa - dist (f a) qa - K ≤ 0"
--       using dense_ge by blast
--     have := calc dist (f a) qa + dist qa pa ≤ dist (f a) pa + 4 * deltaG X"
--       apply (rule dist_along_geodesic[OF geodesic_segmentI[OF H(1)]]) using qa H(1) by auto
--     _ ≤ dist (f a) qa + K + 4 * delta"
--       using I assms by auto
--     finally show ?thesis
--       by (simp add: metric_space_class.dist_commute)
--   qed
--   have B: "dist qb pb ≤ 4 * delta + K"
--   proof -
--     have "dist (f b) pb - dist (f b) qb - K ≤ e" if "e > 0" for e::real
--     proof -
--       have *: "infDist qb G < K + e" using H(2)[OF proj_setD(1)[OF qb]] \<open>e > 0\<close> by auto
--       obtain g where g: "g ∈ G" "dist qb g < K + e"
--         using infDist_almost_attained[OF *] proj_setD(1)[OF \<open>pa ∈ proj_set (f a) G\<close>] by auto
--       have := calc dist (f b) pb ≤ dist (f b) g"
--         unfolding proj_setD(2)[OF \<open>pb ∈ proj_set (f b) G\<close>] using infDist_le[OF \<open>g ∈ G\<close>, of "f b"] by simp
--       _ ≤ dist (f b) qb + dist qb g"
--         by (intro mono_intros)
--       _ ≤ dist (f b) qb + K + e"
--         using g(2) by auto
--       finally show ?thesis by simp
--     qed
--     then have I: "dist (f b) pb - dist (f b) qb - K ≤ 0"
--       using dense_ge by blast
--     have := calc dist (f b) qb + dist qb pb ≤ dist (f b) pb + 4 * deltaG X"
--       apply (rule dist_along_geodesic[OF geodesic_segmentI[OF H(1)]]) using qb H(1) by auto
--     _ ≤ dist (f b) qb + K + 4 * delta"
--       using I assms by auto
--     finally show ?thesis
--       by simp
--   qed
--   have "dist pa pb ≤ dist pa qa + dist qa qb + dist qb pb"
--     by (intro mono_intros)
--   then show ?thesis
--     using Q A B by auto
-- qed
