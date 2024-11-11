/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD -/
import Mathlib.Data.Complex.ExponentialBounds
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
    {Λ C : ℝ} (hf' : QuasiIsometryOn Λ C (Icc a b) f)
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
    {Λ C : ℝ} (hf' : QuasiIsometryOn Λ C (Icc a b) f)
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
      rw [lt_div_iff₀, lt_sub_iff_add_lt, lt_div_iff₀]
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
    let p := G.param (f a)
    have hpa : p 0 = f a := by
      dsimp [p]
      rw [hG.param1]
    have hpb : p (dist (f a) (f b)) = f b := by
      dsimp [p]
      rw [hG.param2]
    obtain ⟨t, htp, ht⟩ : ∃ t : ℝ, x = p t ∧ t ∈ Icc 0 (dist (f a) (f b)) := by
      rw [← hG.param5] at hx
      obtain ⟨t, ht₁, ht₂⟩ := hx
      exact ⟨t, ht₂.symm, ht₁⟩
    let Km : Set X := cthickening D (p '' (Icc 0 t))
    let KM : Set X := cthickening D (p '' (Icc t (dist (f a) (f b))))
    have h₁ : f '' (Icc a b) ⊆ Km ∪ KM := by
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨z, hz, hzx⟩ : ∃ z ∈ G, infDist (f s) G = dist (f s) z :=
        hG.isCompact.exists_infDist_eq_dist hG.nonempty (f s)
      rw [← hG.param5] at hz
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
          rw [hG.param2]
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
    {Λ C : ℝ} (hf' : QuasiIsometryOn Λ C (Icc a b) f)
    {G : Set X} (hG : GeodesicSegmentBetween G (f a) (f b)) :
    hausdorffDist (f '' (Icc a b)) G ≤ 96 * Λ^2 * (C + deltaG X) := by
  sorry
