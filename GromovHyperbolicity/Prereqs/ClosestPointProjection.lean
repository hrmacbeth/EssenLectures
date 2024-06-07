/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
-/
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! ## Closest point projection -/

open Metric
variable {X : Type*} [MetricSpace X]

def proj_set (x : X) (A : Set X) : Set X := {y | y ∈ A ∧ dist x y = infDist x A}

/- The closest point projection of `x` on `A`. It is not unique, so we choose one point realizing the minimal
distance. And if there is no such point, then we use `x`, to make some statements true without any
assumption. -/
-- definition distproj::"'a::metric_space \<Rightarrow> 'a set \<Rightarrow> 'a"
--   where "distproj x A = (if proj_set x A \<noteq> {} then SOME y. y \<in> proj_set x A else x)"

-- lemma proj_setD {x y : X} {A : Set X} (hxy : y ∈ proj_set x A) : y ∈ A ∧ dist x y = infDist x A :=
--   hxy

-- lemma proj_setI:
--   assumes "y \<in> A" "dist x y \<le> infdist x A"
--   shows "y \<in> proj_set x A"
-- using assms infdist_le[OF \<open>y \<in> A\<close>, of x] unfolding proj_set_def by auto

-- lemma proj_setI':
--   assumes "y \<in> A" "\<And>z. z \<in> A \<Longrightarrow> dist x y \<le> dist x z"
--   shows "y \<in> proj_set x A"
-- proof (rule proj_setI[OF \<open>y \<in> A\<close>])
--   show "dist x y \<le> infdist x A"
--     apply (subst infdist_notempty)
--     using assms by (auto intro!: cInf_greatest)
-- qed

-- lemma distproj_in_proj_set:
--   assumes "proj_set x A \<noteq> {}"
--   shows "distproj x A \<in> proj_set x A"
--         "distproj x A \<in> A"
--         "dist x (distproj x A) = infdist x A"
-- proof -
--   show "distproj x A \<in> proj_set x A"
--     using assms unfolding distproj_def using some_in_eq by auto
--   then show "distproj x A \<in> A" "dist x (distproj x A) = infdist x A"
--     unfolding proj_set_def by auto
-- qed

lemma proj_set_nonempty_of_compact {A : Set X} (hA₁ : IsCompact A) (hA : A.Nonempty) (x : X) :
    (proj_set x A).Nonempty := by
  obtain ⟨y, hy⟩ := hA₁.exists_infDist_eq_dist hA x
  exact ⟨y, hy.1, hy.2.symm⟩

-- lemma proj_set_nonempty_of_proper:
--   assumes "proper A" "A \<noteq> {}"
--   shows "proj_set x A \<noteq> {}"
-- proof -
--   have "\<exists>y. y \<in> A \<and> dist x y = infdist x A"
--     using infdist_proper_attained[OF assms, of x] by auto
--   then show "proj_set x A \<noteq> {}" unfolding proj_set_def by auto
-- qed

lemma distproj_self {A : Set X} {x : X} (hx : x ∈ A) : proj_set x A = {x} := sorry
  --       "distproj x A = x" FIXME? skipped this second half
-- proof -
--   show "proj_set x A = {x}"
--     unfolding proj_set_def using assms by auto
--   then show "distproj x A = x"
--     unfolding distproj_def by auto
-- qed

-- lemma distproj_closure [simp]:
--   assumes "x \<in> closure A"
--   shows "distproj x A = x"
-- proof (cases "proj_set x A \<noteq> {}")
--   case True
--   show ?thesis
--     using distproj_in_proj_set(3)[OF True] assms
--     by (metis closure_empty dist_eq_0_iff distproj_self(2) in_closure_iff_infdist_zero)
-- next
--   case False
--   then show ?thesis unfolding distproj_def by auto
-- qed

-- lemma distproj_le:
--   assumes "y \<in> A"
--   shows "dist x (distproj x A) \<le> dist x y"
-- proof (cases "proj_set x A \<noteq> {}")
--   case True
--   show ?thesis using distproj_in_proj_set(3)[OF True] infdist_le[OF assms] by auto
-- next
--   case False
--   then show ?thesis unfolding distproj_def by auto
-- qed

lemma proj_set_dist_le {x y p : X} {A : Set X} (hy : y ∈ A) (hpx : p ∈ proj_set x A) :
    dist x p ≤ dist x y :=
  hpx.2 ▸ infDist_le_dist_of_mem hy
