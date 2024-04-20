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
Gromov product of $x$ and $y$ based at $e$ is the distance between $e$ and the geodesic between
$x$ and $y$. It is also the time after which the geodesics from $e$ to $x$ and from $e$ to $y$
stop travelling together. -/
def Gromov_product_at (e x y : X) : ℝ := (dist e x + dist e y - dist x y) / 2

lemma Gromov_hyperbolic_subsetI2
    (h : ∀ e x y z, e ∈ A → x ∈ A → y ∈ A → z ∈ A →
      Gromov_product_at e x z ≥ min (Gromov_product_at e x y) (Gromov_product_at e y z) - δ) :
    Gromov_hyperbolic_subset δ A := by
  sorry
-- proof (rule Gromov_hyperbolic_subsetI)
--   fix x y z t assume H: "x \∈ A" "z \∈ A" "y \∈ A" "t \∈ A"
--   show "dist x y + dist z t ≤ max (dist x z + dist y t) (dist x t + dist y z) + 2 * delta"
--     using assms[OF H] unfolding Gromov_product_at_def min_def max_def
--     by (auto simp add: divide_simps algebra_simps dist_commute)
-- qed

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

-- [mono_intros]
lemma Gromov_product_le_infDist {x y : X} (h : geodesic_segment_between G x y) :
    Gromov_product_at e x y ≤ infDist e G := by
  sorry
-- proof -
--   have [simp]: "G \<noteq> {}" using assms by auto
--   have "Gromov_product_at e x y ≤ dist e z" if "z \∈ G" for z
--   proof -
--     have "dist e x + dist e y ≤ (dist e z + dist z x) + (dist e z + dist z y)"
--       by (intro add_mono dist_triangle)
--     also have "... = 2 * dist e z + dist x y"
--       apply (auto simp add: dist_commute) using \<open>z \∈ G -/ assms by (metis dist_commute geodesic_segment_dist)
--     finally show ?thesis unfolding Gromov_product_at_def by auto
--   qed
--   then show ?thesis
--     apply (subst infDist_notempty) by (auto intro: cINF_greatest)
-- qed

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
is $4\delta$, independent of the size of the triangle). We prove this basic property
(which, in fact, is a characterization of Gromov-hyperbolic spaces: a geodesic space in which
triangles are thin is hyperbolic). -/
lemma thin_triangles1 {x y z : X}
    (hxy : geodesic_segment_between G x y) (hxz : geodesic_segment_between H x z)
    -- not sure whether inequalities are sharp or non-sharp
    {t : ℝ} (ht₀ : 0 ≤ t) (ht : t ≤ Gromov_product_at x y z) :
    dist (geodesic_segment_param G x t) (geodesic_segment_param H x t) ≤ 4 * δ := by
  sorry
-- proof -
--   have *: "Gromov_product_at x z (geodesic_segment_param H x t) = t"
--     apply (rule Gromov_product_geodesic_segment[OF assms(2)]) using assms(3) Gromov_product_le_dist(2)
--     by (metis atLeastatMost_subset_iff subset_iff)
--   have "Gromov_product_at x y (geodesic_segment_param H x t)
--         ≥ min (Gromov_product_at x y z) (Gromov_product_at x z (geodesic_segment_param H x t)) - δ"
--     by (rule hyperb_ineq)
--   then have I: "Gromov_product_at x y (geodesic_segment_param H x t) ≥ t - δ"
--     using assms(3) unfolding * by auto

--   have *: "Gromov_product_at x (geodesic_segment_param G x t) y = t"
--     apply (subst Gromov_product_commute)
--     apply (rule Gromov_product_geodesic_segment[OF assms(1)]) using assms(3) Gromov_product_le_dist(1)
--     by (metis atLeastatMost_subset_iff subset_iff)
--   have "t - 2 * δ = min t (t- δ) - δ"
--     unfolding min_def using antisym by fastforce
--   also have "... ≤ min (Gromov_product_at x (geodesic_segment_param G x t) y) (Gromov_product_at x y (geodesic_segment_param H x t)) - δ"
--     using I * by (simp add: algebra_simps)
--   also have "... ≤ Gromov_product_at x (geodesic_segment_param G x t) (geodesic_segment_param H x t)"
--     by (rule hyperb_ineq)
--   finally have I: "Gromov_product_at x (geodesic_segment_param G x t) (geodesic_segment_param H x t) ≥ t - 2 * δ"
--     by simp

--   have A: "dist x (geodesic_segment_param G x t) = t"
--     by (meson assms(1) assms(3) atLeastatMost_subset_iff geodesic_segment_param(6) Gromov_product_le_dist(1) subset_eq)
--   have B: "dist x (geodesic_segment_param H x t) = t"
--     by (meson assms(2) assms(3) atLeastatMost_subset_iff geodesic_segment_param(6) Gromov_product_le_dist(2) subset_eq)
--   show ?thesis
--     using I unfolding Gromov_product_at_def A B by auto
-- qed

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

/-- A consequence of the thin triangles property is that, although the geodesic between
two points is in general not unique in a Gromov-hyperbolic space, two such geodesics are
within $O(\delta)$ of each other. -/
lemma geodesics_nearby {x y z : X}
    (hG : geodesic_segment_between G x y)
    (hH : geodesic_segment_between H x y)
    (hz : z ∈ G) :
    infDist z H ≤ 4 * δ := by
  sorry
-- using thin_triangles[OF geodesic_segment_between_x_x(1) assms(2) assms(1) assms(3)]
-- geodesic_segment_endpoints(1)[OF assms(2)] insert_absorb by fastforce

/-- A small variant of the property of thin triangles is that triangles are slim, i.e., there is
a point which is close to the three sides of the triangle (a "center" of the triangle, but
only defined up to $O(\delta)$). And one can take it on any side, and its distance to the corresponding
vertices is expressed in terms of a Gromov product. -/
lemma slim_triangle {x y z : X}
    (hxy : geodesic_segment_between Gxy x y)
    (hxz : geodesic_segment_between Gxz x z)
    (hyz : geodesic_segment_between Gyz y z) :
    ∃ w, infDist w Gxy ≤ 4 * δ ∧ infDist w Gxz ≤ 4 * δ ∧ infDist w Gyz ≤ 4 * δ
      ∧ dist w x = Gromov_product_at x y z ∧ w ∈ Gxy := by
  sorry
-- proof -
--   define w where "w = geodesic_segment_param Gxy x (Gromov_product_at x y z)"
--   have "w ∈ Gxy" unfolding w_def
--     by (rule geodesic_segment_param(3)[OF assms(1)], auto)
--   then have xy: "infDist w Gxy ≤ 4 * δ" by simp
--   have *: "dist w x = (Gromov_product_at x y z)"
--     unfolding w_def using assms(1)
--     by (metis Gromov_product_le_dist(1) Gromov_product_nonneg atLeastAtMost_iff geodesic_segment_param(6) metric_space_class.dist_commute)

--   define w2 where "w2 = geodesic_segment_param Gxz x (Gromov_product_at x y z)"
--   have "w2 ∈ Gxz" unfolding w2_def
--     by (rule geodesic_segment_param(3)[OF assms(2)], auto)
--   moreover have "dist w w2 ≤ 4 * δ"
--     unfolding w_def w2_def by (rule thin_triangles1[OF assms(1) assms(2)], auto)
--   ultimately have xz: "infDist w Gxz ≤ 4 * δ"
--     using infDist_le2 by blast

--   have "w = geodesic_segment_param Gxy y (dist x y - Gromov_product_at x y z)"
--     unfolding w_def by (rule geodesic_segment_reverse_param[OF assms(1), symmetric], auto)
--   then have w: "w = geodesic_segment_param Gxy y (Gromov_product_at y x z)"
--     using Gromov_product_add[of x y z] by (metis add_diff_cancel_left')

--   define w3 where "w3 = geodesic_segment_param Gyz y (Gromov_product_at y x z)"
--   have "w3 ∈ Gyz" unfolding w3_def
--     by (rule geodesic_segment_param(3)[OF assms(3)], auto)
--   moreover have "dist w w3 ≤ 4 * δ"
--     unfolding w w3_def by (rule thin_triangles1[OF geodesic_segment_commute[OF assms(1)] assms(3)], auto)
--   ultimately have yz: "infDist w Gyz ≤ 4 * δ"
--     using infDist_le2 by blast

--   show ?thesis using xy xz yz * \<open>w ∈ Gxy -/ by force
-- qed

/-- The distance of a vertex of a triangle to the opposite side is essentially given by the
Gromov product, up to $2\delta$. -/
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
following sense: if one has a union of three geodesics from $x$ to $t$, then a geodesic from $x$
to $t$ remains within distance $8\delta$ of the union of these 3 geodesics. We formulate the
statement in geodesic hyperbolic spaces as the proof requires the construction of an additional
geodesic, but in fact the statement is true without this assumption, thanks to the Bonk-Schramm
extension theorem. -/
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

/-! There are converses to the above statements: if triangles are thin, or slim, then the space
is Gromov-hyperbolic, for some $\delta$. We prove these criteria here, following the proofs in
Ghys (with a simplification in the case of slim triangles. -/

/-- The basic result we will use twice below is the following: if points on sides of triangles
at the same distance of the basepoint are close to each other up to the Gromov product, then the
space is hyperbolic. The proof goes as follows. One wants to show that $(x,z)_e \geq
\min((x,y)_e, (y,z)_e) - \delta = t-\delta$. On $[ex]$, $[ey]$ and $[ez]$, consider points
$wx$, $wy$ and $wz$ at distance $t$ of $e$. Then $wx$ and $wy$ are $\delta$-close by assumption,
and so are $wy$ and $wz$. Then $wx$ and $wz$ are $2\delta$-close. One can use these two points
to express $(x,z)_e$, and the result follows readily. -/
lemma controlled_thin_triangles_implies_hyperbolic [GeodesicSpace X]
    (h : ∀ (x y z : X) t Gxy Gxz, geodesic_segment_between Gxy x y
      → geodesic_segment_between Gxz x z → 0 ≤ t → t ≤ Gromov_product_at x y z
      → dist (geodesic_segment_param Gxy x t) (geodesic_segment_param Gxz x t) ≤ δ) :
    Gromov_hyperbolic_subset δ (Set.univ : Set X) := by
  sorry
-- proof (rule Gromov_hyperbolic_subsetI2)
--   fix e x y z::'a
--   define t where "t = min (Gromov_product_at e x y) (Gromov_product_at e y z)"
--   define wx where "wx = geodesic_segment_param {e--x} e t"
--   define wy where "wy = geodesic_segment_param {e--y} e t"
--   define wz where "wz = geodesic_segment_param {e--z} e t"
--   have "dist wx wy ≤ delta"
--     unfolding wx_def wy_def t_def by (rule assms[of _ _ x _ y], auto)
--   have "dist wy wz ≤ delta"
--     unfolding wy_def wz_def t_def by (rule assms[of _ _ y _ z], auto)

--   have "t + dist wy x = dist e wx + dist wy x"
--     unfolding wx_def apply (auto intro!: geodesic_segment_param_in_geodesic_spaces(6)[symmetric])
--     unfolding t_def by (auto, meson Gromov_product_le_dist(1) min.absorb_iff2 min.left_idem order.trans)
--   also have "... ≤ dist e wx + (dist wy wx + dist wx x)"
--     by (intro mono_intros)
--   also have "... ≤ dist e wx + (delta + dist wx x)"
--     using \<open>dist wx wy ≤ delta -/ by (auto simp add: metric_space_class.dist_commute)
--   also have "... = delta + dist e x"
--     apply auto apply (rule geodesic_segment_dist[of "{e--x}"])
--     unfolding wx_def t_def by (auto simp add: geodesic_segment_param_in_segment)
--   finally have *: "t + dist wy x - delta ≤ dist e x" by simp

--   have "t + dist wy z = dist e wz + dist wy z"
--     unfolding wz_def apply (auto intro!: geodesic_segment_param_in_geodesic_spaces(6)[symmetric])
--     unfolding t_def by (auto, meson Gromov_product_le_dist(2) min.absorb_iff1 min.right_idem order.trans)
--   also have "... ≤ dist e wz + (dist wy wz + dist wz z)"
--     by (intro mono_intros)
--   also have "... ≤ dist e wz + (delta + dist wz z)"
--     using \<open>dist wy wz ≤ delta -/ by (auto simp add: metric_space_class.dist_commute)
--   also have "... = delta + dist e z"
--     apply auto apply (rule geodesic_segment_dist[of "{e--z}"])
--     unfolding wz_def t_def by (auto simp add: geodesic_segment_param_in_segment)
--   finally have "t + dist wy z - delta ≤ dist e z" by simp

--   then have "(t + dist wy x - delta) + (t + dist wy z - delta) ≤ dist e x + dist e z"
--     using * by simp
--   also have "... = dist x z + 2 * Gromov_product_at e x z"
--     unfolding Gromov_product_at_def by (auto simp add: algebra_simps divide_simps)
--   also have "... ≤ dist wy x + dist wy z + 2 * Gromov_product_at e x z"
--     using metric_space_class.dist_triangle[of x z wy] by (auto simp add: metric_space_class.dist_commute)
--   finally have "2 * t - 2 * delta ≤ 2 * Gromov_product_at e x z"
--     by auto
--   then show "min (Gromov_product_at e x y) (Gromov_product_at e y z) - delta ≤ Gromov_product_at e x z"
--     unfolding t_def by auto
-- qed

/-- We prove that if triangles are thin, i.e., they satisfy the Rips condition, i.e., every side
of a triangle is included in the $\delta$-neighborhood of the union of the other triangles, then
the space is hyperbolic. If a point $w$ on $[xy]$ satisfies $d(x,w) < (y,z)_x - \delta$, then its
friend on $[xz] \cup [yz]$ has to be on $[xz]$, and roughly at the same distance of the origin.
Then it follows that the point on $[xz]$ with $d(x,w') = d(x,w)$ is close to $w$, as desired.
If $d(x,w) \in [(y,z)_x - \delta, (y,z)_x)$, we argue in the same way but for the point which
is closer to $x$ by an amount $\delta$. Finally, the last case $d(x,w) = (y,z)_x$ follows by
continuity. -/
theorem thin_triangles_implies_hyperbolic [GeodesicSpace X]
    (h : ∀ (x y z w : X) Gxy Gyz Gxz, geodesic_segment_between Gxy x y
      → geodesic_segment_between Gxz x z → geodesic_segment_between Gyz y z
      → w ∈ Gxy → infDist w (Gxz ∪ Gyz) ≤ δ) :
    Gromov_hyperbolic_subset (4 * δ) (Set.univ : Set X) := by
  sorry
-- proof -
--   obtain x0::'a where True by auto
--   have "infDist x0 ({x0} ∪ {x0}) ≤ delta"
--     by (rule assms[of "{x0}" x0 x0 "{x0}" x0 "{x0}" x0], auto)
--   then have [simp]: "delta \<ge> 0"
--     using infDist_nonneg by auto

--   have "dist (geodesic_segment_param Gxy x t) (geodesic_segment_param Gxz x t) ≤ 4 * delta"
--     if H: "geodesic_segment_between Gxy x y" "geodesic_segment_between Gxz x z" "t ∈ {0..Gromov_product_at x y z}"
--     for x y z t Gxy Gxz
--   proof -
--     have Main: "dist (geodesic_segment_param Gxy x u) (geodesic_segment_param Gxz x u) ≤ 4 * delta"
--       if "u ∈ {delta..<Gromov_product_at x y z}" for u
--     proof -
--       define wy where "wy = geodesic_segment_param Gxy x (u-delta)"
--       have "dist wy (geodesic_segment_param Gxy x u) = abs((u-delta) - u)"
--         unfolding wy_def apply (rule geodesic_segment_param(7)[OF H(1)]) using that apply auto
--         using Gromov_product_le_dist(1)[of x y z] \<open>delta \<ge> 0 -/ by linarith+
--       then have I1: "dist wy (geodesic_segment_param Gxy x u) = delta" by auto

--       have "infDist wy (Gxz ∪ {y--z}) ≤ delta"
--         unfolding wy_def apply (rule assms[of Gxy x y _ z]) using H by (auto simp add: geodesic_segment_param_in_segment)
--       moreover have "\<exists>wz ∈ Gxz ∪ {y--z}. infDist wy (Gxz ∪ {y--z}) = dist wy wz"
--         apply (rule infDist_proper_attained, intro proper_Un)
--         using H(2) by (auto simp add: geodesic_segment_topology)
--       ultimately obtain wz where wz: "wz ∈ Gxz ∪ {y--z}" "dist wy wz ≤ delta"
--         by force

--       have "dist wz x ≤ dist wz wy + dist wy x"
--         by (rule metric_space_class.dist_triangle)
--       also have "... ≤ delta + (u-delta)"
--         apply (intro add_mono) using wz(2) unfolding wy_def apply (auto simp add: metric_space_class.dist_commute)
--         apply (intro eq_refl geodesic_segment_param(6)[OF H(1)])
--         using that apply auto
--         by (metis diff_0_right diff_mono dual_order.trans Gromov_product_le_dist(1) less_eq_real_def metric_space_class.dist_commute metric_space_class.zero_le_dist wy_def)
--       finally have "dist wz x ≤ u" by auto
--       also have "... < Gromov_product_at x y z"
--         using that by auto
--       also have "... ≤ infDist x {y--z}"
--         by (rule Gromov_product_le_infDist, auto)
--       finally have "dist x wz < infDist x {y--z}"
--         by (simp add: metric_space_class.dist_commute)
--       then have "wz \<notin> {y--z}"
--         by (metis add.left_neutral infDist_triangle infDist_zero leD)
--       then have "wz ∈ Gxz"
--         using wz by auto

--       have "u - delta = dist x wy"
--         unfolding wy_def apply (rule geodesic_segment_param(6)[symmetric, OF H(1)])
--         using that apply auto
--         using Gromov_product_le_dist(1)[of x y z] \<open>delta \<ge> 0 -/ by linarith
--       also have "... ≤ dist x wz + dist wz wy"
--         by (rule metric_space_class.dist_triangle)
--       also have "... ≤ dist x wz + delta"
--         using wz(2) by (simp add: metric_space_class.dist_commute)
--       finally have "dist x wz \<ge> u - 2 * delta" by auto

--       define dz where "dz = dist x wz"
--       have *: "wz = geodesic_segment_param Gxz x dz"
--         unfolding dz_def using \<open>wz ∈ Gxz -/ H(2) by auto
--       have "dist wz (geodesic_segment_param Gxz x u) = abs(dz - u)"
--         unfolding * apply (rule geodesic_segment_param(7)[OF H(2)])
--         unfolding dz_def using \<open>dist wz x ≤ u -/ that apply (auto simp add: metric_space_class.dist_commute)
--         using Gromov_product_le_dist(2)[of x y z] \<open>delta \<ge> 0 -/ by linarith+
--       also have "... ≤ 2 * delta"
--         unfolding dz_def using \<open>dist wz x ≤ u -/ \<open>dist x wz \<ge> u - 2 * delta -/
--         by (auto simp add: metric_space_class.dist_commute)
--       finally have I3: "dist wz (geodesic_segment_param Gxz x u) ≤ 2 * delta"
--         by simp

--       have "dist (geodesic_segment_param Gxy x u) (geodesic_segment_param Gxz x u)
--               ≤ dist (geodesic_segment_param Gxy x u) wy + dist wy wz + dist wz (geodesic_segment_param Gxz x u)"
--         by (rule dist_triangle4)
--       also have "... ≤ delta + delta + (2 * delta)"
--         using I1 wz(2) I3 by (auto simp add: metric_space_class.dist_commute)
--       finally show ?thesis by simp
--     qed
--     have "t ∈ {0..dist x y}" "t ∈ {0..dist x z}" "t \<ge> 0"
--       using \<open>t ∈ {0..Gromov_product_at x y z} -/ apply auto
--       using Gromov_product_le_dist[of x y z] by linarith+
--     consider "t ≤ delta" | "t ∈ {delta..<Gromov_product_at x y z}" | "t = Gromov_product_at x y z \<and> t > delta"
--       using \<open>t ∈ {0..Gromov_product_at x y z} -/ by (auto, linarith)
--     then show ?thesis
--     proof (cases)
--       case 1
--       have "dist (geodesic_segment_param Gxy x t) (geodesic_segment_param Gxz x t) ≤ dist x (geodesic_segment_param Gxy x t) + dist x (geodesic_segment_param Gxz x t)"
--         by (rule metric_space_class.dist_triangle3)
--       also have "... = t + t"
--         using geodesic_segment_param(6)[OF H(1) \<open>t ∈ {0..dist x y} -/] geodesic_segment_param(6)[OF H(2) \<open>t ∈ {0..dist x z} -/]
--         by auto
--       also have "... ≤ 4 * delta" using 1 \<open>delta \<ge> 0 -/ by linarith
--       finally show ?thesis by simp
--     next
--       case 2
--       show ?thesis using Main[OF 2] by simp
--     next
--       case 3
--       /-- In this case, we argue by approximating $t$ by a slightly smaller parameter, for which
--       the result has already been proved above. We need to argue that all functions are continuous
--       on the sets we are considering, which is straightforward but tedious. -/
--       define u::"nat \<Rightarrow> real" where "u = (\<lambda>n. t-1/n)"
--       have "u \<longlonglongrightarrow> t - 0"
--         unfolding u_def by (intro tendsto_intros)
--       then have "u \<longlonglongrightarrow> t" by simp
--       then have *: "eventually (\<lambda>n. u n > delta) sequentially"
--         using 3 by (auto simp add: order_tendsto_iff)
--       have **: "eventually (\<lambda>n. u n \<ge> 0) sequentially"
--         apply (rule eventually_elim2[OF *, of "(\<lambda>n. delta \<ge> 0)"]) apply auto
--         using \<open>delta \<ge> 0 -/ by linarith
--       have ***: "u n ≤ t" for n unfolding u_def by auto
--       have A: "eventually (\<lambda>n. u n ∈ {delta..<Gromov_product_at x y z}) sequentially"
--         apply (auto intro!: eventually_conj)
--         apply (rule eventually_mono[OF *], simp)
--         unfolding u_def using 3 by auto
--       have B: "eventually (\<lambda>n. dist (geodesic_segment_param Gxy x (u n)) (geodesic_segment_param Gxz x (u n)) ≤ 4 * delta) sequentially"
--         by (rule eventually_mono[OF A Main], simp)
--       have C: "(\<lambda>n. dist (geodesic_segment_param Gxy x (u n)) (geodesic_segment_param Gxz x (u n)))
--             \<longlonglongrightarrow> dist (geodesic_segment_param Gxy x t) (geodesic_segment_param Gxz x t)"
--         apply (intro tendsto_intros)
--         apply (rule continuous_on_tendsto_compose[OF _ \<open>u \<longlonglongrightarrow> t -/ \<open>t ∈ {0..dist x y} -/])
--         apply (simp add: isometry_on_continuous H(1))
--         using ** *** \<open>t ∈ {0..dist x y} -/ apply (simp, intro eventually_conj, simp, meson dual_order.trans eventually_mono)
--         apply (rule continuous_on_tendsto_compose[OF _ \<open>u \<longlonglongrightarrow> t -/ \<open>t ∈ {0..dist x z} -/])
--         apply (simp add: isometry_on_continuous H(2))
--         using ** *** \<open>t ∈ {0..dist x z} -/ apply (simp, intro eventually_conj, simp, meson dual_order.trans eventually_mono)
--         done
--       show ?thesis
--         using B unfolding eventually_sequentially using LIMSEQ_le_const2[OF C] by simp
--     qed
--   qed
--   with controlled_thin_triangles_implies_hyperbolic[OF this]
--   show ?thesis by auto
-- qed

/-- Then, we prove that if triangles are slim (i.e., there is a point that is $\delta$-close to
all sides), then the space is hyperbolic. Using the previous statement, we should show that points
on $[xy]$ and $[xz]$ at the same distance $t$ of the origin are close, if $t \leq (y,z)_x$.
There are two steps:
- for $t = (y,z)_x$, then the two points are in fact close to the middle of the triangle
(as this point satisfies $d(x,y) = d(x,w) + d(w,y) + O(\delta)$, and similarly for the other sides,
one gets readily $d(x,w) = (y,z)_w + O(\delta)$ by expanding the formula for the Gromov product).
Hence, they are close together.
- For $t < (y,z)_x$, we argue that there are points $y' \in [xy]$ and $z' \in [xz]$ for which
$t = (y',z')_x$, by a continuity argument and the intermediate value theorem.
Then the result follows from the first step in the triangle $xy'z'$.

The proof we give is simpler than the one in~\<^cite> "ghys_hyperbolique", and gives better constants. -/
theorem slim_triangles_implies_hyperbolic [GeodesicSpace X]
    (h : ∀ (x y z : X) Gxy Gyz Gxz, geodesic_segment_between Gxy x y
      → geodesic_segment_between Gxz x z → geodesic_segment_between Gyz y z
      → ∃ w, infDist w Gxy ≤ delta ∧ infDist w Gxz ≤ delta ∧ infDist w Gyz ≤ delta) :
    Gromov_hyperbolic_subset (6 * delta) (Set.univ : Set X) := by
  sorry
-- proof -
--   /-- First step: the result is true for $t = (y,z)_x$. -/
--   have Main: "dist (geodesic_segment_param Gxy x (Gromov_product_at x y z)) (geodesic_segment_param Gxz x (Gromov_product_at x y z)) ≤ 6 * delta"
--     if H: "geodesic_segment_between Gxy x y" "geodesic_segment_between Gxz x z"
--     for x y z Gxy Gxz
--   proof -
--     obtain w where w: "infDist w Gxy ≤ delta" "infDist w Gxz ≤ delta" "infDist w {y--z} ≤ delta"
--       using assms[OF H, of "{y--z}"] by auto
--     have "\<exists>wxy ∈ Gxy. infDist w Gxy = dist w wxy"
--       apply (rule infDist_proper_attained) using H(1) by (auto simp add: geodesic_segment_topology)
--     then obtain wxy where wxy: "wxy ∈ Gxy" "dist w wxy ≤ delta"
--       using w by auto
--     have "\<exists>wxz ∈ Gxz. infDist w Gxz = dist w wxz"
--       apply (rule infDist_proper_attained) using H(2) by (auto simp add: geodesic_segment_topology)
--     then obtain wxz where wxz: "wxz ∈ Gxz" "dist w wxz ≤ delta"
--       using w by auto
--     have "\<exists>wyz ∈ {y--z}. infDist w {y--z} = dist w wyz"
--       apply (rule infDist_proper_attained) by (auto simp add: geodesic_segment_topology)
--     then obtain wyz where wyz: "wyz ∈ {y--z}" "dist w wyz ≤ delta"
--       using w by auto

--     have I: "dist wxy wxz ≤ 2 * delta" "dist wxy wyz ≤ 2 * delta" "dist wxz wyz ≤ 2 * delta"
--       using metric_space_class.dist_triangle[of wxy wxz w] metric_space_class.dist_triangle[of wxy wyz w] metric_space_class.dist_triangle[of wxz wyz w]
--             wxy(2) wyz(2) wxz(2) by (auto simp add: metric_space_class.dist_commute)

--     /-- We show that $d(x, wxy)$ is close to the Gromov product of $y$ and $z$ seen from $x$.
--     This follows from the fact that $w$ is essentially on all geodesics, so that everything simplifies
--     when one writes down the Gromov products, leaving only $d(x, w)$ up to $O(\delta)$.
--     To get the right $O(\delta)$, one has to be a little bit careful, using the triangular inequality
--     when possible. This means that the computations for the upper and lower bounds are different,
--     making them a little bit tedious, although straightforward. -/
--     have "dist y wxy -4 * delta + dist wxy z ≤ dist y wxy - dist wxy wyz + dist wxy z - dist wxy wyz"
--       using I by simp
--     also have "... ≤ dist wyz y + dist wyz z"
--       using metric_space_class.dist_triangle[of y wxy wyz] metric_space_class.dist_triangle[of wxy z wyz]
--       by (auto simp add: metric_space_class.dist_commute)
--     also have "... = dist y z"
--       using wyz(1) by (metis geodesic_segment_dist local.some_geodesic_is_geodesic_segment(1) metric_space_class.dist_commute)
--     finally have *: "dist y wxy + dist wxy z - 4 * delta ≤ dist y z" by simp
--     have "2 * Gromov_product_at x y z = dist x y + dist x z - dist y z"
--       unfolding Gromov_product_at_def by simp
--     also have "... ≤ dist x wxy + dist wxy y + dist x wxy + dist wxy z - (dist y wxy + dist wxy z - 4 * delta)"
--       using metric_space_class.dist_triangle[of x y wxy] metric_space_class.dist_triangle[of x z wxy] *
--       by (auto simp add: metric_space_class.dist_commute)
--     also have "... = 2 * dist x wxy + 4 * delta"
--       by (auto simp add: metric_space_class.dist_commute)
--     finally have A: "Gromov_product_at x y z ≤ dist x wxy + 2 * delta" by simp

--     have "dist x wxy -4 * delta + dist wxy z ≤ dist x wxy - dist wxy wxz + dist wxy z - dist wxy wxz"
--       using I by simp
--     also have "... ≤ dist wxz x + dist wxz z"
--       using metric_space_class.dist_triangle[of x wxy wxz] metric_space_class.dist_triangle[of wxy z wxz]
--       by (auto simp add: metric_space_class.dist_commute)
--     also have "... = dist x z"
--       using wxz(1) H(2) by (metis geodesic_segment_dist metric_space_class.dist_commute)
--     finally have *: "dist x wxy + dist wxy z - 4 * delta ≤ dist x z" by simp
--     have "2 * dist x wxy - 4 * delta = (dist x wxy + dist wxy y) + (dist x wxy + dist wxy z - 4 * delta) - (dist y wxy + dist wxy z)"
--       by (auto simp add: metric_space_class.dist_commute)
--     also have "... ≤ dist x y + dist x z - dist y z"
--       using * metric_space_class.dist_triangle[of y z wxy] geodesic_segment_dist[OF H(1) wxy(1)] by auto
--     also have "... = 2 * Gromov_product_at x y z"
--       unfolding Gromov_product_at_def by simp
--     finally have B: "Gromov_product_at x y z \<ge> dist x wxy - 2 * delta" by simp

--     define dy where "dy = dist x wxy"
--     have *: "wxy = geodesic_segment_param Gxy x dy"
--       unfolding dy_def using \<open>wxy ∈ Gxy -/ H(1) by auto
--     have "dist wxy (geodesic_segment_param Gxy x (Gromov_product_at x y z)) = abs(dy - Gromov_product_at x y z)"
--       unfolding * apply (rule geodesic_segment_param(7)[OF H(1)])
--       unfolding dy_def using that geodesic_segment_dist_le[OF H(1) wxy(1), of x] by (auto simp add: metric_space_class.dist_commute)
--     also have "... ≤ 2 * delta"
--       using A B unfolding dy_def by auto
--     finally have Iy: "dist wxy (geodesic_segment_param Gxy x (Gromov_product_at x y z)) ≤ 2 * delta"
--       by simp

--     /-- We need the same estimate for $wxz$. The proof is exactly the same, copied and pasted.
--     It would be better to have a separate statement, but since its assumptions would be rather
--     cumbersome I decided to keep the two proofs. -/
--     have "dist z wxz -4 * delta + dist wxz y ≤ dist z wxz - dist wxz wyz + dist wxz y - dist wxz wyz"
--       using I by simp
--     also have "... ≤ dist wyz z + dist wyz y"
--       using metric_space_class.dist_triangle[of z wxz wyz] metric_space_class.dist_triangle[of wxz y wyz]
--       by (auto simp add: metric_space_class.dist_commute)
--     also have "... = dist z y"
--       using \<open>dist wyz y + dist wyz z = dist y z -/ by (auto simp add: metric_space_class.dist_commute)
--     finally have *: "dist z wxz + dist wxz y - 4 * delta ≤ dist z y" by simp
--     have "2 * Gromov_product_at x y z = dist x z + dist x y - dist z y"
--       unfolding Gromov_product_at_def by (simp add: metric_space_class.dist_commute)
--     also have "... ≤ dist x wxz + dist wxz z + dist x wxz + dist wxz y - (dist z wxz + dist wxz y - 4 * delta)"
--       using metric_space_class.dist_triangle[of x z wxz] metric_space_class.dist_triangle[of x y wxz] *
--       by (auto simp add: metric_space_class.dist_commute)
--     also have "... = 2 * dist x wxz + 4 * delta"
--       by (auto simp add: metric_space_class.dist_commute)
--     finally have A: "Gromov_product_at x y z ≤ dist x wxz + 2 * delta" by simp

--     have "dist x wxz -4 * delta + dist wxz y ≤ dist x wxz - dist wxz wxy + dist wxz y - dist wxz wxy"
--       using I by (simp add: metric_space_class.dist_commute)
--     also have "... ≤ dist wxy x + dist wxy y"
--       using metric_space_class.dist_triangle[of x wxz wxy] metric_space_class.dist_triangle[of wxz y wxy]
--       by (auto simp add: metric_space_class.dist_commute)
--     also have "... = dist x y"
--       using wxy(1) H(1) by (metis geodesic_segment_dist metric_space_class.dist_commute)
--     finally have *: "dist x wxz + dist wxz y - 4 * delta ≤ dist x y" by simp
--     have "2 * dist x wxz - 4 * delta = (dist x wxz + dist wxz z) + (dist x wxz + dist wxz y - 4 * delta) - (dist z wxz + dist wxz y)"
--       by (auto simp add: metric_space_class.dist_commute)
--     also have "... ≤ dist x z + dist x y - dist z y"
--       using * metric_space_class.dist_triangle[of z y wxz] geodesic_segment_dist[OF H(2) wxz(1)] by auto
--     also have "... = 2 * Gromov_product_at x y z"
--       unfolding Gromov_product_at_def by (simp add: metric_space_class.dist_commute)
--     finally have B: "Gromov_product_at x y z \<ge> dist x wxz - 2 * delta" by simp

--     define dz where "dz = dist x wxz"
--     have *: "wxz = geodesic_segment_param Gxz x dz"
--       unfolding dz_def using \<open>wxz ∈ Gxz -/ H(2) by auto
--     have "dist wxz (geodesic_segment_param Gxz x (Gromov_product_at x y z)) = abs(dz - Gromov_product_at x y z)"
--       unfolding * apply (rule geodesic_segment_param(7)[OF H(2)])
--       unfolding dz_def using that geodesic_segment_dist_le[OF H(2) wxz(1), of x] by (auto simp add: metric_space_class.dist_commute)
--     also have "... ≤ 2 * delta"
--       using A B unfolding dz_def by auto
--     finally have Iz: "dist wxz (geodesic_segment_param Gxz x (Gromov_product_at x y z)) ≤ 2 * delta"
--       by simp

--     have "dist (geodesic_segment_param Gxy x (Gromov_product_at x y z)) (geodesic_segment_param Gxz x (Gromov_product_at x y z))
--       ≤ dist (geodesic_segment_param Gxy x (Gromov_product_at x y z)) wxy + dist wxy wxz + dist wxz (geodesic_segment_param Gxz x (Gromov_product_at x y z))"
--       by (rule dist_triangle4)
--     also have "... ≤ 2 * delta + 2 * delta + 2 * delta"
--       using Iy Iz I by (auto simp add: metric_space_class.dist_commute)
--     finally show ?thesis by simp
--   qed

--   /-- Second step: the result is true for $t \leq (y,z)_x$, by a continuity argument and a
--   reduction to the first step. -/
--   have "dist (geodesic_segment_param Gxy x t) (geodesic_segment_param Gxz x t) ≤ 6 * delta"
--     if H: "geodesic_segment_between Gxy x y" "geodesic_segment_between Gxz x z" "t ∈ {0..Gromov_product_at x y z}"
--     for x y z t Gxy Gxz
--   proof -
--     define ys where "ys = (\<lambda>s. geodesic_segment_param Gxy x (s * dist x y))"
--     define zs where "zs = (\<lambda>s. geodesic_segment_param Gxz x (s * dist x z))"
--     define F where "F = (\<lambda>s. Gromov_product_at x (ys s) (zs s))"
--     have "\<exists>s. 0 ≤ s \<and> s ≤ 1 \<and> F s = t"
--     proof (rule IVT')
--       show "F 0 ≤ t" "t ≤ F 1"
--         unfolding F_def using that unfolding ys_def zs_def by (auto simp add: Gromov_product_e_x_x)
--       show "continuous_on {0..1} F"
--         unfolding F_def Gromov_product_at_def ys_def zs_def
--         apply (intro continuous_intros continuous_on_compose2[of "{0..dist x y}" _ _ "\<lambda>t. t * dist x y"] continuous_on_compose2[of "{0..dist x z}" _ _ "\<lambda>t. t * dist x z"])
--         apply (auto intro!: isometry_on_continuous geodesic_segment_param(4) that)
--         using metric_space_class.zero_le_dist mult_left_le_one_le by blast+
--     qed (simp)
--     then obtain s where s: "s ∈ {0..1}" "t = Gromov_product_at x (ys s) (zs s)"
--       unfolding F_def by auto

--     have a: "x = geodesic_segment_param Gxy x 0" using H(1) by auto
--     have b: "x = geodesic_segment_param Gxz x 0" using H(2) by auto
--     have dy: "dist x (ys s) = s * dist x y"
--       unfolding ys_def apply (rule geodesic_segment_param[OF H(1)]) using s(1) by (auto simp add: mult_left_le_one_le)
--     have dz: "dist x (zs s) = s * dist x z"
--       unfolding zs_def apply (rule geodesic_segment_param[OF H(2)]) using s(1) by (auto simp add: mult_left_le_one_le)

--     define Gxy2 where "Gxy2 = geodesic_subsegment Gxy x 0 (s * dist x y)"
--     define Gxz2 where "Gxz2 = geodesic_subsegment Gxz x 0 (s * dist x z)"

--     have "dist (geodesic_segment_param Gxy2 x t) (geodesic_segment_param Gxz2 x t) ≤ 6 * delta"
--     unfolding s(2) proof (rule Main)
--       show "geodesic_segment_between Gxy2 x (ys s)"
--         apply (subst a) unfolding Gxy2_def ys_def apply (rule geodesic_subsegment[OF H(1)])
--         using s(1) by (auto simp add: mult_left_le_one_le)
--       show "geodesic_segment_between Gxz2 x (zs s)"
--         apply (subst b) unfolding Gxz2_def zs_def apply (rule geodesic_subsegment[OF H(2)])
--         using s(1) by (auto simp add: mult_left_le_one_le)
--     qed
--     moreover have "geodesic_segment_param Gxy2 x (t-0) = geodesic_segment_param Gxy x t"
--       apply (subst a) unfolding Gxy2_def apply (rule geodesic_subsegment(3)[OF H(1)])
--       using s(1) H(3) unfolding s(2) apply (auto simp add: mult_left_le_one_le)
--       unfolding dy[symmetric] by (rule Gromov_product_le_dist)
--     moreover have "geodesic_segment_param Gxz2 x (t-0) = geodesic_segment_param Gxz x t"
--       apply (subst b) unfolding Gxz2_def apply (rule geodesic_subsegment(3)[OF H(2)])
--       using s(1) H(3) unfolding s(2) apply (auto simp add: mult_left_le_one_le)
--       unfolding dz[symmetric] by (rule Gromov_product_le_dist)
--     ultimately show ?thesis by simp
--   qed
--   with controlled_thin_triangles_implies_hyperbolic[OF this]
--   show ?thesis by auto
-- qed
