/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD -/
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.MetricSpace.HausdorffDistance
import GromovHyperbolicity.Prereqs

/-!
# Gromov hyperbolic spaces
-/

open Metric

noncomputable section

/-! ## Definition, basic properties

Although we will mainly work with type classes later on, we introduce the definition
of hyperbolicity on subsets of a metric space.

Two important references on this topic are~\<^cite>"ghys_hyperbolique" and~\<^cite> "bridson_haefliger".
We will sometimes follow them, sometimes depart from them.
-/

section
variable {X : Type*} [MetricSpace X]

/--
A set is δ-hyperbolic if it satisfies the following inequality. It is very obscure at first sight,
but we will see several equivalent characterizations later on. For instance, a space is hyperbolic
(maybe for a different constant δ) if all geodesic triangles are thin, i.e., every side is
close to the union of the two other sides. This definition captures the main features of negative
curvature at a large scale, and has proved extremely fruitful and influential. -/
def Gromov_hyperbolic_subset (δ : ℝ) (A : Set X) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, ∀ t ∈ A,
  dist x y + dist z t ≤ max (dist x z + dist y t) (dist x t + dist y z) + 2 * δ

variable {δ : ℝ} {A : Set X}

-- [intro]
set_option maxHeartbeats 5000 in
lemma Gromov_hyperbolic_subsetI
    (h : ∀ x y z t, x ∈ A → y ∈ A → z ∈ A → t ∈ A → dist x y + dist z t ≤ max (dist x z + dist y t) (dist x t + dist y z) + 2 * δ) :
    Gromov_hyperbolic_subset δ A := by
  aesop (add unfold safe Gromov_hyperbolic_subset)
-- using assms unfolding Gromov_hyperbolic_subset_def by auto

/-- When the four points are not all distinct, the above inequality is always satisfied for δ = 0.-/
lemma Gromov_hyperbolic_ineq_not_distinct {x y z t : X}
    (h : x = y ∨ x = z ∨ x = t ∨ y = z ∨ y = t ∨ z = t) :
    dist x y + dist z t ≤ max (dist x z + dist y t) (dist x t + dist y z) := by
  have := dist_triangle z x t
  have := dist_triangle x z y
  aesop (add simp [dist_comm, add_comm])
-- using assms by (auto simp add: dist_commute, simp add: dist_triangle add.commute, simp add: dist_triangle3)

/-- It readily follows from the definition that hyperbolicity passes to the closure of the set. -/
lemma Gromov_hyperbolic_closure (h : Gromov_hyperbolic_subset δ A) :
    Gromov_hyperbolic_subset δ (closure A) := by
  let f : X × X × X × X → ℝ := fun p ↦ dist p.1 p.2.1 + dist p.2.2.1 p.2.2.2
  -- after `fun_prop` bugfix go back to
  -- let f : X × X × X × X → ℝ := fun (x, y, z, t) ↦ dist x y + dist z t
  have hf : Continuous f := by fun_prop
  let g : X × X × X × X → ℝ := fun p ↦
    max (dist p.1 p.2.2.1 + dist p.2.1 p.2.2.2) (dist p.1 p.2.2.2 + dist p.2.1 p.2.2.1) + 2 * δ
  -- let g : X × X × X × X → ℝ :=
  --   fun (x, y, z, t) ↦ max (dist x z + dist y t) (dist x t + dist y z) + 2 * δ
  have hg : Continuous g := by fun_prop
  intro x hx y hy z hz t ht
  have hxyzt : (x, y, z, t) ∈ closure (A ×ˢ (A ×ˢ (A ×ˢ A))) := by
    simp only [closure_prod_eq, Set.mem_prod]
    tauto
  refine le_on_closure (f := f) (g := g) ?_ hf.continuousOn hg.continuousOn hxyzt
  rintro ⟨x, y, z, t⟩ ⟨hx, hy, hz, ht⟩
  exact h x hx y hy z hz t ht
-- unfolding Gromov_hyperbolic_subset_def proof (auto)
--   fix x y z t assume H: "x \∈ closure A" "y \∈ closure A" "z \∈ closure A" "t \∈ closure A"
--   obtain X::"nat \<Rightarrow> 'a" where X: "∧n. X n \∈ A" "X \<longlonglongrightarrow> x"
--     using H closure_sequential by blast
--   obtain Y::"nat \<Rightarrow> 'a" where Y: "∧n. Y n \∈ A" "Y \<longlonglongrightarrow> y"
--     using H closure_sequential by blast
--   obtain Z::"nat \<Rightarrow> 'a" where Z: "∧n. Z n \∈ A" "Z \<longlonglongrightarrow> z"
--     using H closure_sequential by blast
--   obtain T::"nat \<Rightarrow> 'a" where T: "∧n. T n \∈ A" "T \<longlonglongrightarrow> t"
--     using H closure_sequential by blast
--   have *: "max (dist (X n) (Z n) + dist (Y n) (T n)) (dist (X n) (T n) + dist (Y n) (Z n)) + 2 * delta - dist (X n) (Y n) - dist (Z n) (T n) ≥ 0" for n
--     using assms X(1)[of n] Y(1)[of n] Z(1)[of n] T(1)[of n] unfolding Gromov_hyperbolic_subset_def
--     by (auto simp add: algebra_simps)
--   have **: "(\<lambda>n. max (dist (X n) (Z n) + dist (Y n) (T n)) (dist (X n) (T n) + dist (Y n) (Z n)) + 2 * delta - dist (X n) (Y n) - dist (Z n) (T n))
--     \<longlonglongrightarrow> max (dist x z + dist y t) (dist x t + dist y z) + 2 * delta - dist x y - dist z t"
--     apply (auto intro!: tendsto_intros) using X Y Z T by auto
--   have "max (dist x z + dist y t) (dist x t + dist y z) + 2 * delta - dist x y - dist z t ≥ 0"
--     apply (rule LIMSEQ_le_const[OF **]) using * by auto
--   then show "dist x y + dist z t ≤ max (dist x z + dist y t) (dist x t + dist y z) + 2 * delta"
--     by auto
-- qed

/-- A good formulation of hyperbolicity is in terms of Gromov products. Intuitively, the
Gromov product of `x` and `y` based at `e` is the distance between `e` and the geodesic between
`x` and `y`. It is also the time after which the geodesics from `e` to `x` and from `e` to `y`
stop travelling together. -/
def Gromov_product_at (e x y : X) : ℝ := (dist e x + dist e y - dist x y) / 2

-- [mono_intros]
@[simp] lemma Gromov_product_nonneg (e x y : X) : Gromov_product_at e x y ≥ 0 := by
  have := dist_triangle x e y
  simp only [Gromov_product_at, ge_iff_le]
  cancel_denoms
  simpa [dist_comm, add_comm] using this
-- unfolding Gromov_product_at_def by (simp add: dist_triangle3)

lemma Gromov_product_commute (e x y : X) : Gromov_product_at e x y = Gromov_product_at e y x := by
  simp only [Gromov_product_at, dist_comm, add_comm]
-- unfolding Gromov_product_at_def by (auto simp add: dist_commute)

-- [mono_intros]
@[simp] lemma Gromov_product_le_dist (e x y : X) :
    Gromov_product_at e x y ≤ dist e x ∧ Gromov_product_at e x y ≤ dist e y := by
  have := dist_triangle e x y
  have := dist_triangle e y x
  simp only [Gromov_product_at, dist_comm] at *
  constructor <;> linarith
-- unfolding Gromov_product_at_def by (auto simp add: diff_le_eq dist_triangle dist_triangle2)

lemma Gromov_product_add (e x y : X) :
    Gromov_product_at e x y + Gromov_product_at x e y = dist e x := by
  simp only [Gromov_product_at, dist_comm]
  ring
-- unfolding Gromov_product_at_def by (auto simp add: algebra_simps divide_simps dist_commute)

-- not sure whether inequalities are sharp or non-sharp
lemma Gromov_product_geodesic_segment {x y : X}
    (h : geodesic_segment_between G x y) {t : ℝ} (ht₀ : 0 ≤ t) (ht : t ≤ dist x y) :
    Gromov_product_at x y (geodesic_segment_param G x t) = t := by
  sorry
-- proof -
--   have "dist x (geodesic_segment_param G x t) = t"
--     using assms(1) assms(2) geodesic_segment_param(6) by auto
--   moreover have "dist y (geodesic_segment_param G x t) = dist x y - t"
--     by (metis \<open>dist x (geodesic_segment_param G x t) = t -/ add_diff_cancel_left' assms(1) assms(2) dist_commute geodesic_segment_dist geodesic_segment_param(3))
--   ultimately show ?thesis unfolding Gromov_product_at_def by auto
-- qed

@[simp] lemma Gromov_product_e_x_x (e x : X) : Gromov_product_at e x x = dist e x := by
  simp [Gromov_product_at]
-- unfolding Gromov_product_at_def by auto

lemma Gromov_product_at_diff (x y z a b c : X) :
    |Gromov_product_at x y z - Gromov_product_at a b c| ≤ dist x a + dist y b + dist z c := by
  sorry
-- unfolding Gromov_product_at_def abs_le_iff apply (auto simp add: divide_simps)
-- by (smt dist_commute dist_triangle4)+

lemma Gromov_product_at_diff1 (x y a b : X) :
    |Gromov_product_at a x y - Gromov_product_at b x y| ≤ dist a b := by
  have := Gromov_product_at_diff a x y b x y
  aesop
-- using Gromov_product_at_diff[of a x y b x y] by auto

lemma Gromov_product_at_diff2 (e x y z : X) :
    |Gromov_product_at e x z - Gromov_product_at e y z| ≤ dist x y := by
  have := Gromov_product_at_diff e x z e y z
  aesop
-- using Gromov_product_at_diff[of e x z e y z] by auto

lemma Gromov_product_at_diff3 (e x y z : X) :
    |Gromov_product_at e x y - Gromov_product_at e x z| ≤ dist y z := by
  have := Gromov_product_at_diff e x y e x z
  aesop
-- using Gromov_product_at_diff[of e x y e x z] by auto

open Filter Topology in
/-- The Gromov product is continuous in its three variables. We formulate it in terms of sequences,
as it is the way it will be used below (and moreover continuity for functions of several variables
is very poor in the library). -/
@[fun_prop] lemma Gromov_product_at_continuous :
    -- {u v w : ι → X} (l : Filter ι)
    -- (h1 : Tendsto u l (𝓝 x)) (h2 : Tendsto v l (𝓝 y)) (h3 : Tendsto w l (𝓝 z)) :
    -- Tendsto (fun n ↦ Gromov_product_at (u n) (v n) (w n)) l (𝓝 (Gromov_product_at x y z)) := by
    Continuous (fun (p : X × X × X) ↦ Gromov_product_at p.1 p.2.1 p.2.2) := by
    -- Continuous (fun ((x, y, z) : X × X × X) ↦ Gromov_product_at x y z) := by
  simp only [Gromov_product_at]
  fun_prop (disch := norm_num)
-- proof -
--   have "((\<lambda>n. abs(Gromov_product_at (u n) (v n) (w n) - Gromov_product_at x y z)) \<longlongrightarrow> 0 + 0 + 0) F"
--     apply (rule tendsto_sandwich[of "\<lambda>n. 0" _ _ "\<lambda>n. dist (u n) x + dist (v n) y + dist (w n) z", OF always_eventually always_eventually])
--     apply (simp, simp add: Gromov_product_at_diff, simp, intro tendsto_intros)
--     using assms tendsto_dist_iff by auto
--   then show ?thesis
--     apply (subst tendsto_dist_iff) unfolding dist_real_def by auto
-- qed

end

/-! ## Typeclass for Gromov hyperbolic spaces -/

-- We could (should?) just derive `Gromov_hyperbolic_space` from `metric_space`.
-- However, in this case, properties of metric spaces are not available when working in the locale!
-- It is more efficient to ensure that we have a metric space by putting a type class restriction
-- in the definition. The δ in Gromov-hyperbolicity type class is called `deltaG` to
-- avoid name clashes.

-- class metric_space_with_deltaG = metric_space +
--   fixes deltaG::"('a::metric_space) itself \<Rightarrow> real"

class Gromov_hyperbolic_space (X : Type*) [MetricSpace X] where
  deltaG : ℝ
  hyperb_quad_ineq0 : Gromov_hyperbolic_subset deltaG (Set.univ : Set X)

-- class Gromov_hyperbolic_space_geodesic = Gromov_hyperbolic_space + geodesic_space

variable {X : Type*} [MetricSpace X] [Gromov_hyperbolic_space X]

-- set_option quotPrecheck false in
local notation "δ" => Gromov_hyperbolic_space.deltaG X

-- [mono_intros]
lemma Gromov_hyperbolic_space.hyperb_quad_ineq (x y z t : X) :
    dist x y + dist z t ≤ max (dist x z + dist y t) (dist x t + dist y z) + 2 * δ := by
  apply Gromov_hyperbolic_space.hyperb_quad_ineq0 <;> aesop
-- using hyperb_quad_ineq0 unfolding Gromov_hyperbolic_subset_def by auto

/-- It readily follows from the definition that the completion of a δ-hyperbolic
space is still δ-hyperbolic. -/
instance deltaG_metric_completion : Gromov_hyperbolic_space (UniformSpace.Completion X) where
  deltaG := δ
  hyperb_quad_ineq0 := by
    apply Gromov_hyperbolic_subsetI
    intro x y z t
    simp only [Set.mem_univ, forall_true_left]
    induction x, y, z, t using UniformSpace.Completion.induction_on₄
    · apply isClosed_le <;> fun_prop
    · simp only [UniformSpace.Completion.dist_eq]
      apply Gromov_hyperbolic_space.hyperb_quad_ineq
-- instance proof (standard, rule Gromov_hyperbolic_subsetI)
--   have "Gromov_hyperbolic_subset δ (range (to_metric_completion::'a \<Rightarrow> _))"
--     unfolding Gromov_hyperbolic_subset_def
--     apply (auto simp add: isometry_onD[OF to_metric_completion_isometry])
--     by (metis hyperb_quad_ineq)
--   then have "Gromov_hyperbolic_subset (deltaG TYPE('a metric_completion)) (UNIV::'a metric_completion set)"
--     unfolding deltaG_metric_completion_def to_metric_completion_dense'[symmetric]
--     using Gromov_hyperbolic_closure by auto
--   then show "dist x y + dist z t ≤ max (dist x z + dist y t) (dist x t + dist y z) + 2 * deltaG TYPE('a metric_completion)"
--       for x y z t::"'a metric_completion"
--     unfolding Gromov_hyperbolic_subset_def by auto
-- qed

open Gromov_hyperbolic_space
-- begin

--  [mono_intros]
variable (X) in -- TODO `positivity` attribute
@[simp] lemma delta_nonneg [Inhabited X] : δ ≥ 0 := by
  let x : X := default
  have := hyperb_quad_ineq x x x x
  aesop
-- proof -
--   obtain x::'a where True by auto
--   show ?thesis using hyperb_quad_ineq[of x x x x] by auto
-- qed

-- [mono_intros]
lemma hyperb_ineq (e x y z : X) :
    Gromov_product_at e x z ≥ min (Gromov_product_at e x y) (Gromov_product_at e y z) - δ := by
  have H := hyperb_quad_ineq e y x z
  simp only [Gromov_product_at, dist_comm, ← max_add_add_right, ← min_sub_sub_right,
    le_max_iff, min_le_iff] at *
  refine Or.elim H (fun _ => Or.inr ?_) (fun _ => Or.inl ?_) <;>
  · cancel_denoms
    rw [← sub_nonpos] at *
    abel_nf at *
    assumption
-- using hyperb_quad_ineq[of e y x z] unfolding Gromov_product_at_def min_def max_def
-- by (auto simp add: divide_simps algebra_simps metric_space_class.dist_commute)

-- [mono_intros]
lemma hyperb_ineq' (e x y z : X) :
    Gromov_product_at e x z + δ ≥ min (Gromov_product_at e x y) (Gromov_product_at e y z) := by
  have := hyperb_ineq e x y z
  aesop
-- using hyperb_ineq[of e x y z] by auto

-- [mono_intros]
lemma hyperb_ineq_4_points [Inhabited X] (e x y z t : X) :
    min (Gromov_product_at e x y) (min (Gromov_product_at e y z) (Gromov_product_at e z t)) - 2 * δ
    ≤ Gromov_product_at e x t := by
  have h1 := hyperb_ineq e x y z
  have h2 := hyperb_ineq e x z t
  have := delta_nonneg X
  simp only [← min_sub_sub_right, min_le_iff] at *
  by_contra!
  obtain h1a | h1b := h1 <;> obtain h2a | h2b := h2 <;> linarith
-- using hyperb_ineq[of e x y z] hyperb_ineq[of e x z t] apply auto using delta_nonneg by linarith

-- [mono_intros]
lemma hyperb_ineq_4_points' [Inhabited X] (e x y z t : X) :
    min (Gromov_product_at e x y) (min (Gromov_product_at e y z) (Gromov_product_at e z t))
    ≤ Gromov_product_at e x t + 2 * δ := by
  have := hyperb_ineq_4_points e x y z t
  aesop
-- using hyperb_ineq_4_points[of e x y z t] by auto

/-- In Gromov-hyperbolic spaces, geodesic triangles are thin, i.e., a point on one side of a
geodesic triangle is close to the union of the two other sides (where the constant in "close"
is `4 * δ`, independent of the size of the triangle). We prove this basic property
(which, in fact, is a characterization of Gromov-hyperbolic spaces: a geodesic space in which
triangles are thin is hyperbolic). -/
lemma thin_triangles1 [Inhabited X] {x y z : X}
    (hxy : geodesic_segment_between G x y) (hxz : geodesic_segment_between H x z)
    -- not sure whether inequalities are sharp or non-sharp
    {t : ℝ} (ht₀ : 0 ≤ t) (ht : t ≤ Gromov_product_at x y z) :
    dist (geodesic_segment_param G x t) (geodesic_segment_param H x t) ≤ 4 * δ := by
  have h1 : Gromov_product_at x z (geodesic_segment_param H x t) = t := by
    apply Gromov_product_geodesic_segment hxz ht₀
    have := Gromov_product_le_dist x y z
    linarith
  have : min (Gromov_product_at x y z) (Gromov_product_at x z (geodesic_segment_param H x t)) - δ
      ≤ Gromov_product_at x y (geodesic_segment_param H x t) := hyperb_ineq ..
  have I : t - δ ≤ Gromov_product_at x y (geodesic_segment_param H x t) := by
    rwa [h1, min_eq_right ht] at this
  have h2 : Gromov_product_at x (geodesic_segment_param G x t) y = t := by
    rw [Gromov_product_commute]
    apply Gromov_product_geodesic_segment hxy ht₀
    have := Gromov_product_le_dist x y z
    linarith
  have I :=
  calc t - 2 * δ = min t (t- δ) - δ := by
        rw [min_eq_right]
        · ring
        · have : 0 ≤ δ := delta_nonneg X
          linarith
    _ ≤ min (Gromov_product_at x (geodesic_segment_param G x t) y)
          (Gromov_product_at x y (geodesic_segment_param H x t)) - δ := by
        rw [h2]
        gcongr
    _ ≤ Gromov_product_at x (geodesic_segment_param G x t) (geodesic_segment_param H x t) :=
        hyperb_ineq ..
  have A : dist x (geodesic_segment_param G x t) = t := by
    apply le_antisymm
    · apply dist_geodesic_segment_param
    conv_lhs => rw [← h2]
    exact (Gromov_product_le_dist _ _ _).1
  have B : dist x (geodesic_segment_param H x t) = t := by
    apply le_antisymm
    · apply dist_geodesic_segment_param
    conv_lhs => rw [← h2]
    exact (Gromov_product_le_dist _ _ _).1
  rw [Gromov_product_at] at I
  linarith

-- needed later in this file
theorem thin_triangles {x y z w : X}
    (hxy : geodesic_segment_between Gxy x y)
    (hxz : geodesic_segment_between Gxz x z)
    (hyz : geodesic_segment_between Gyz y z)
    (hw : w ∈ Gyz) :
    infDist w (Gxy ∪ Gxz) ≤ 4 * δ := by
  sorry
-- proof -
--   obtain t where w: "t ∈ {0..dist y z}" "w = geodesic_segment_param Gyz y t"
--     using geodesic_segment_param[OF assms(3)] assms(4) by (metis imageE)
--   show ?thesis
--   proof (cases "t ≤ Gromov_product_at y x z")
--     case True
--     have *: "dist w (geodesic_segment_param Gxy y t) ≤ 4 * δ" unfolding w(2)
--       apply (rule thin_triangles1[of _ _ z _ x])
--       using True assms(1) assms(3) w(1) by (auto simp add: geodesic_segment_commute Gromov_product_commute)
--     show ?thesis
--       apply (rule infDist_le2[OF _ *])
--       by (metis True assms(1) box_real(2) geodesic_segment_commute geodesic_segment_param(3) Gromov_product_le_dist(1) mem_box_real(2) order_trans subset_eq sup.cobounded1 w(1))
--   next
--     case False
--     define s where "s = dist y z - t"
--     have s: "s ∈ {0..Gromov_product_at z y x}"
--       unfolding s_def using Gromov_product_add[of y z x] w(1) False by (auto simp add: Gromov_product_commute)
--     have w2: "w = geodesic_segment_param Gyz z s"
--       unfolding s_def w(2) apply (rule geodesic_segment_reverse_param[symmetric]) using assms(3) w(1) by auto
--     have *: "dist w (geodesic_segment_param Gxz z s) ≤ 4 * δ" unfolding w2
--       apply (rule thin_triangles1[of _ _ y _ x])
--       using s assms by (auto simp add: geodesic_segment_commute)
--     show ?thesis
--       apply (rule infDist_le2[OF _ *])
--       by (metis Un_iff assms(2) atLeastAtMost_iff geodesic_segment_commute geodesic_segment_param(3) Gromov_product_commute Gromov_product_le_dist(1) order_trans s)
--   qed
-- qed


/-- The distance of a vertex of a triangle to the opposite side is essentially given by the
Gromov product, up to $2\delta$. -/
-- needed later in this file
lemma dist_triangle_side_middle {x y : X} (z : X) (hxy : geodesic_segment_between G x y) :
    dist z (geodesic_segment_param G x (Gromov_product_at x z y))
    ≤ Gromov_product_at z x y + 2 * δ := by
  sorry
-- proof -
--   define m where "m = geodesic_segment_param G x (Gromov_product_at x z y)"
--   have "m ∈ G"
--     unfolding m_def using assms(1) by auto
--   have A: "dist x m = Gromov_product_at x z y"
--     unfolding m_def by (rule geodesic_segment_param(6)[OF assms(1)], auto)
--   have B: "dist y m = dist x y - dist x m"
--     using geodesic_segment_dist[OF assms \<open>m ∈ G -/] by (auto simp add: metric_space_class.dist_commute)
--   have *: "dist x z + dist y m = Gromov_product_at z x y + dist x y"
--           "dist x m + dist y z = Gromov_product_at z x y + dist x y"
--     unfolding B A Gromov_product_at_def by (auto simp add: metric_space_class.dist_commute divide_simps)

--   have "dist x y + dist z m ≤ max (dist x z + dist y m) (dist x m + dist y z) + 2 * δ"
--     by (rule hyperb_quad_ineq)
--   then have "dist z m ≤ Gromov_product_at z x y + 2 * δ"
--     unfolding * by auto
--   then show ?thesis
--     unfolding m_def by auto
-- qed

-- [mono_intros]
-- needed for `dist_along_quasiconvex`
lemma infDist_triangle_side {x y : X} (z : X) (hxy : geodesic_segment_between G x y) :
    infDist z G ≤ Gromov_product_at z x y + 2 * δ := by
  sorry
-- proof -
--   have "infDist z G ≤ dist z (geodesic_segment_param G x (Gromov_product_at x z y))"
--     using assms by (auto intro!: infDist_le)
--   then show ?thesis
--     using dist_triangle_side_middle[OF assms, of z] by auto
-- qed

/-- The distance of a point on a side of triangle to the opposite vertex is controlled by
the length of the opposite sides, up to $\delta$. -/
-- needed for `Morse_Gromov_theorem_aux2`
lemma dist_le_max_dist_triangle {x y m : X} (hxy : geodesic_segment_between G x y) (hm : m ∈ G) :
    dist m z ≤ max (dist x z) (dist y z) + δ := by
  sorry
-- proof -
--   consider "dist m x ≤ δ" | "dist m y ≤ δ" |
--            "dist m x ≥ δ ∧ dist m y ≥ δ ∧ Gromov_product_at z x m ≤ Gromov_product_at z m y" |
--            "dist m x ≥ δ ∧ dist m y ≥ δ ∧ Gromov_product_at z m y ≤ Gromov_product_at z x m"
--     by linarith
--   then show ?thesis
--   proof (cases)
--     case 1
--     have "dist m z ≤ dist m x + dist x z"
--       by (intro mono_intros)
--     then show ?thesis using 1 by auto
--   next
--     case 2
--     have "dist m z ≤ dist m y + dist y z"
--       by (intro mono_intros)
--     then show ?thesis using 2 by auto
--   next
--     case 3
--     then have "Gromov_product_at z x m = min (Gromov_product_at z x m) (Gromov_product_at z m y)"
--       by auto
--     also have "... ≤ Gromov_product_at z x y + δ"
--       by (intro mono_intros)
--     finally have "dist z m ≤ dist z y + dist x m - dist x y + 2 * δ"
--       unfolding Gromov_product_at_def by (auto simp add: divide_simps algebra_simps)
--     also have "... = dist z y - dist m y + 2 * δ"
--       using geodesic_segment_dist[OF assms] by auto
--     also have "... ≤ dist z y + δ"
--       using 3 by auto
--     finally show ?thesis
--       by (simp add: metric_space_class.dist_commute)
--   next
--     case 4
--     then have "Gromov_product_at z m y = min (Gromov_product_at z x m) (Gromov_product_at z m y)"
--       by auto
--     also have "... ≤ Gromov_product_at z x y + δ"
--       by (intro mono_intros)
--     finally have "dist z m ≤ dist z x + dist m y - dist x y + 2 * δ"
--       unfolding Gromov_product_at_def by (auto simp add: divide_simps algebra_simps)
--     also have "... = dist z x - dist x m + 2 * δ"
--       using geodesic_segment_dist[OF assms] by auto
--     also have "... ≤ dist z x + δ"
--       using 4 by (simp add: metric_space_class.dist_commute)
--     finally show ?thesis
--       by (simp add: metric_space_class.dist_commute)
--   qed
-- qed

/-- A useful variation around the previous properties is that quadrilaterals are thin, in the
following sense: if one has a union of three geodesics from `x` to $t$, then a geodesic from `x`
to $t$ remains within distance $8\delta$ of the union of these 3 geodesics. We formulate the
statement in geodesic hyperbolic spaces as the proof requires the construction of an additional
geodesic, but in fact the statement is true without this assumption, thanks to the Bonk-Schramm
extension theorem. -/
-- needed for `quasiconvex_thickening`
lemma thin_quadrilaterals [GeodesicSpace X] {x y z t w : X}
    (hxy : geodesic_segment_between Gxy x y)
    (hyz : geodesic_segment_between Gyz y z)
    (hzt : geodesic_segment_between Gzt z t)
    (hxt : geodesic_segment_between Gxt x t)
    (hw : w ∈ Gxt) :
    infDist w (Gxy ∪ Gyz ∪ Gzt) ≤ 8 * δ := by
  sorry
-- proof -
--   have I: "infDist w ({x--z} ∪ Gzt) ≤ 4 * δ"
--     apply (rule thin_triangles[OF _ assms(3) assms(4) assms(5)])
--     by (simp add: geodesic_segment_commute)
--   have "\<exists>u ∈ {x--z} ∪ Gzt. infDist w ({x--z} ∪ Gzt) = dist w u"
--     apply (rule infDist_proper_attained, auto intro!: proper_Un simp add: geodesic_segment_topology(7))
--     by (meson assms(3) geodesic_segmentI geodesic_segment_topology)
--   then obtain u where u: "u ∈ {x--z} ∪ Gzt" "infDist w ({x--z} ∪ Gzt) = dist w u"
--     by auto
--   have "infDist u (Gxy ∪ Gyz ∪ Gzt) ≤ 4 * δ"
--   proof (cases "u ∈ {x--z}")
--     case True
--     have "infDist u (Gxy ∪ Gyz ∪ Gzt) ≤ infDist u (Gxy ∪ Gyz)"
--       apply (intro mono_intros) using assms(1) by auto
--     also have "... ≤ 4 * δ"
--       using thin_triangles[OF geodesic_segment_commute[OF assms(1)] assms(2) _ True] by auto
--     finally show ?thesis
--       by auto
--   next
--     case False
--     then have *: "u ∈ Gzt" using u(1) by auto
--     have "infDist u (Gxy ∪ Gyz ∪ Gzt) ≤ infDist u Gzt"
--       apply (intro mono_intros) using assms(3) by auto
--     also have "... = 0" using * by auto
--     finally show ?thesis
--       using local.delta_nonneg by linarith
--   qed
--   moreover have "infDist w (Gxy ∪ Gyz ∪ Gzt) ≤ infDist u (Gxy ∪ Gyz ∪ Gzt) + dist w u"
--     by (intro mono_intros)
--   ultimately show ?thesis
--     using I u(2) by auto
-- qed
