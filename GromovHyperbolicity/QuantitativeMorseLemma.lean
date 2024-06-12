/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD -/
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Util.Time
import GromovHyperbolicity.QuasigeodesicBound

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
the fact that the closest point projection on quasi-convex sets is exponentially contracting). -/

variable {X : Type*} [MetricSpace X] [GromovHyperbolicSpace X] [GeodesicSpace X]

open GromovHyperbolicSpace

/-- The main induction is over. To conclude, one should apply its result to the original
geodesic segment joining the points $f(a)$ and $f(b)$. -/
lemma Morse_Gromov_theorem_aux1
    {f : ℝ → X} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    {Λ C : ℝ} (hf' : quasi_isometry_on Λ C (Icc a b) f)
    (hab : a ≤ b)
    {G : Set X} (hGf : GeodesicSegmentBetween G (f a) (f b))
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

  calc infDist (f z) G
      ≤ gromovProductAt (f z) (f a) (f b) + 2 * deltaG X := infDist_triangle_side _ hGf
    _ ≤ (Λ^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (-K * (b - a)))) + 2 * δ := by
        gcongr
        exact Morse_Gromov_theorem_aux0 hf hf' hab hz hδ
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
    {G : Set X} (hG : GeodesicSegmentBetween G (f a) (f b)) :
    hausdorffDist (f '' (Icc a b)) G ≤ Λ^2 * (11/2 * C + 96 * deltaG X) := by
  have := hf'.C_nonneg
  have := hf'.one_le_lambda
  have : Inhabited X := ⟨f a⟩
  have h_delta := delta_nonneg X
  by_cases hab : b < a
  · have : Icc a b = ∅ := Icc_eq_empty_of_lt hab
    rw [this] at *
    simp
    positivity
  push_neg at hab
  have key {δ : ℝ} (hδ : δ > deltaG X) {z : ℝ} (hz : z ∈ Icc a b) :
      infDist (f z) G ≤ Λ^2 * (11/2 * C + 95 * δ) :=
    Morse_Gromov_theorem_aux1 hf hf' hab hG hz hδ
  let D : ℝ := Λ^2 * (11/2 * C + 95 * deltaG X)
  have : D ≥ 0 := by positivity
  have I {z : ℝ} (hz : z ∈ Icc a b) : infDist (f z) G ≤ D := by
    apply le_of_forall_le_of_dense
    intro c hc
    let δ : ℝ := (c / Λ ^ 2 - 11 / 2 * C) / 95
    refine le_trans (key (δ := δ) ?_ hz) ?_
    · dsimp [δ]
      dsimp [D] at hc
      change _ < _
      rw [lt_div_iff, lt_sub_iff_add_lt, lt_div_iff]
      · linarith only [hc]
      all_goals positivity
    · dsimp [δ]
      have : 0 < Λ := by positivity
      ring_nf
      field_simp
  apply hausdorffDist_le_of_infDist
  · positivity
  · rintro _ ⟨z, hz₁, rfl⟩
    calc _ ≤ _ := I hz₁
      _ ≤ _ := by
          dsimp [D]
          have : 0 ≤ Λ ^ 2 * deltaG X := by positivity
          linarith only [this]
  · intro x hx
    calc infDist x (f '' (Icc a b)) ≤ D + 1 * deltaG X := ?_
        _ ≤ D + Λ^2 * deltaG X := by gcongr; nlinarith only [hf'.one_le_lambda]
        _ = _ := by dsimp [D]; ring
    let p := geodesic_segment_param G (f a)
    have hpa : p 0 = f a := by
      dsimp [p]
      rw [geodesic_segment_param1 hG]
    have hpb : p (dist (f a) (f b)) = f b := by
      dsimp [p]
      rw [geodesic_segment_param2 hG]
    obtain ⟨t, htp, ht⟩ : ∃ t : ℝ, x = p t ∧ t ∈ Icc 0 (dist (f a) (f b)) := by
      rw [← geodesic_segment_param5 hG] at hx
      obtain ⟨t, ht₁, ht₂⟩ := hx
      exact ⟨t, ht₂.symm, ht₁⟩
    let Km : Set X := cthickening D (p '' (Icc 0 t))
    let KM : Set X := cthickening D (p '' (Icc t (dist (f a) (f b))))
    have h₁ : f '' (Icc a b) ⊆ Km ∪ KM := by
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨z, hz, hzx⟩ : ∃ z ∈ G, infDist (f s) G = dist (f s) z :=
        (geodesic_segment_topology ⟨_, _, hG⟩).1.exists_infDist_eq_dist
          (geodesic_segment_topology ⟨_, _, hG⟩).2.2.2.2.2 (f s)
      rw [← geodesic_segment_param5 hG] at hz
      change z ∈ p '' _ at hz
      obtain ⟨tz, htz, rfl⟩ := hz
      have := I hs
      rw [hzx] at this
      obtain htz' | htz' := le_or_gt tz t
      · left
        refine mem_cthickening_of_dist_le (f s) (p tz) _ _ ?_ this
        apply mem_image_of_mem
        exact ⟨htz.1, htz'⟩
      · right
        refine mem_cthickening_of_dist_le (f s) (p tz) _ _ ?_ this
        apply mem_image_of_mem
        exact ⟨htz'.le, htz.2⟩
    have h₂ : f '' (Icc a b) = (Km ∩ f '' (Icc a b)) ∪ (KM ∩ f '' (Icc a b)) := by aesop --sorry -- by auto
    have h₃ : ((Km ∩ f '' (Icc a b)) ∩ (KM ∩ f '' (Icc a b))).Nonempty := by
      suffices (f '' Icc a b ∩ (Km ∩ KM)).Nonempty by
        convert this using 1
        ext x
        set A := f '' (Icc a b)
        clear_value Km KM A
        simp
        tauto
      have h₄ : IsPreconnected (f '' (Icc a b)) := (isPreconnected_Icc).image f hf
      rw [isPreconnected_closed_iff] at h₄
      apply h₄
      · exact isClosed_cthickening
      · exact isClosed_cthickening
      · apply h₁
      · use f a
        refine ⟨mem_image_of_mem _ ?_, self_subset_cthickening _ ?_⟩
        · exact ⟨le_refl _, hab⟩
        · rw [← hpa]
          apply mem_image_of_mem
          exact ⟨le_refl _, ht.1⟩
      · use f b
        refine ⟨mem_image_of_mem _ ?_, self_subset_cthickening _ ?_⟩
        · exact ⟨hab, le_refl _⟩
        · rw [← hpb]
          apply mem_image_of_mem
          refine ⟨ht.2, ?_⟩
          dsimp [p]
          rw [geodesic_segment_param2 hG]
    obtain ⟨y, hy⟩ : ∃ y, y ∈ f '' (Icc a b) ∧ y ∈ Km ∧ y ∈ KM := by
      obtain ⟨y, hy⟩ := h₃
      exact ⟨y, hy.1.2, hy.1.1, hy.2.1⟩
    obtain ⟨tm, htm⟩ : ∃ tm, tm ∈ Icc 0 t ∧ dist (p tm) y ≤ D := by
      have h₁ : IsCompact (p '' (Icc 0 t)) := sorry
      have h₂ : (p '' (Icc 0 t)).Nonempty := sorry
      obtain ⟨z, ⟨tm, htm, rfl⟩, htmz⟩ := h₁.exists_infDist_eq_dist h₂ y
      refine ⟨tm, htm, ?_⟩
      rw [dist_comm, ← htmz, ← mem_cthickening_iff_infDist_le]
      · exact hy.2.1
      · assumption
      · exact h₂
    obtain ⟨tM, htM⟩ : ∃ tM, tM ∈ Icc t (dist (f a) (f b)) ∧ dist (p tM) y ≤ D := by
      have h₁ : IsCompact (p '' (Icc t (dist (f a) (f b)))) := sorry
      have h₂ : (p '' (Icc t (dist (f a) (f b)))).Nonempty := sorry
      obtain ⟨z, ⟨tm, htm, rfl⟩, htmz⟩ := h₁.exists_infDist_eq_dist h₂ y
      refine ⟨tm, htm, ?_⟩
      rw [dist_comm, ← htmz, ← mem_cthickening_iff_infDist_le]
      · exact hy.2.2
      · assumption
      · exact h₂
    let H := p '' Icc tm tM
    have h_H : GeodesicSegmentBetween H (p tm) (p tM) := by
      dsimp [H]
      have : tm ≤ tM := htm.1.2.trans htM.1.1
      rw [← geodesic_subsegment1 hG htm.1.1 this htM.1.2]
      apply geodesic_subsegment2 hG htm.1.1 this htM.1.2
    have : x ∈ H := by
      rw [htp]
      dsimp [H]
      apply mem_image_of_mem
      exact ⟨htm.1.2, htM.1.1⟩
    calc infDist x (f '' (Icc a b)) ≤ dist x y := infDist_le_dist_of_mem hy.1
      _ ≤ max (dist (p tm) y) (dist (p tM) y) + deltaG X :=
          dist_le_max_dist_triangle h_H this y
      _ ≤ _ := by
          gcongr
          · simp [htm.2, htM.2]
          · linarith only []

/-- The full statement of the Morse-Gromov Theorem, asserting that a quasi-geodesic is
within controlled distance of a geodesic with the same endpoints. It is given in the formulation
of Shchur~\<^cite>\<open>"shchur"\<close>, with optimal control in terms of the parameters of the quasi-isometry.
This statement follows readily from the previous one and from the fact that quasi-geodesics can be
approximated by Lipschitz ones. -/
theorem Morse_Gromov_theorem
    {f : ℝ → X} {a b : ℝ}
    {Λ C : ℝ} (hf' : quasi_isometry_on Λ C (Icc a b) f)
    {G : Set X} (hG : GeodesicSegmentBetween G (f a) (f b)) :
    hausdorffDist (f '' (Icc a b)) G ≤ 96 * Λ^2 * (C + deltaG X) := by
  sorry
#exit
proof -
  have C: "C ≥ 0" "lambda ≥ 1" using quasi_isometry_onD[OF assms(1)] by auto
  consider "dist (f a) (f b) ≥ 2 * C ∧ a ≤ b" | "dist (f a) (f b) ≤ 2 * C ∧ a ≤ b" | "b < a"
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
