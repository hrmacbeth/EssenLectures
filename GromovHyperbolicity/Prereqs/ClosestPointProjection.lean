/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
-/
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! ## Closest point projection -/

open Metric
variable {X : Type*} [MetricSpace X]

def projSet (x : X) (A : Set X) : Set X := {y | y ∈ A ∧ dist x y = infDist x A}

/- The closest point projection of `x` on `A`. It is not unique, so we choose one point realizing the minimal
distance. And if there is no such point, then we use `x`, to make some statements true without any
assumption. -/
-- definition distproj::"'a::metric_space \<Rightarrow> 'a set \<Rightarrow> 'a"
--   where "distproj x A = (if projSet x A \<noteq> {} then SOME y. y \<in> projSet x A else x)"

-- lemma projSetD {x y : X} {A : Set X} (hxy : y ∈ projSet x A) : y ∈ A ∧ dist x y = infDist x A :=
--   hxy

-- lemma projSetI:
--   assumes "y \<in> A" "dist x y \<le> infdist x A"
--   shows "y \<in> projSet x A"
-- using assms infdist_le[OF \<open>y \<in> A\<close>, of x] unfolding projSet_def by auto

-- lemma projSetI':
--   assumes "y \<in> A" "\<And>z. z \<in> A \<Longrightarrow> dist x y \<le> dist x z"
--   shows "y \<in> projSet x A"
-- proof (rule projSetI[OF \<open>y \<in> A\<close>])
--   show "dist x y \<le> infdist x A"
--     apply (subst infdist_notempty)
--     using assms by (auto intro!: cInf_greatest)
-- qed

-- lemma distproj_in_projSet:
--   assumes "projSet x A \<noteq> {}"
--   shows "distproj x A \<in> projSet x A"
--         "distproj x A \<in> A"
--         "dist x (distproj x A) = infdist x A"
-- proof -
--   show "distproj x A \<in> projSet x A"
--     using assms unfolding distproj_def using some_in_eq by auto
--   then show "distproj x A \<in> A" "dist x (distproj x A) = infdist x A"
--     unfolding projSet_def by auto
-- qed

lemma projSet_nonempty_of_compact {A : Set X} (hA₁ : IsCompact A) (hA : A.Nonempty) (x : X) :
    (projSet x A).Nonempty := by
  obtain ⟨y, hy⟩ := hA₁.exists_infDist_eq_dist hA x
  exact ⟨y, hy.1, hy.2.symm⟩

-- lemma projSet_nonempty_of_proper:
--   assumes "proper A" "A \<noteq> {}"
--   shows "projSet x A \<noteq> {}"
-- proof -
--   have "\<exists>y. y \<in> A \<and> dist x y = infdist x A"
--     using infdist_proper_attained[OF assms, of x] by auto
--   then show "projSet x A \<noteq> {}" unfolding projSet_def by auto
-- qed

lemma distproj_self {A : Set X} {x : X} (hx : x ∈ A) : projSet x A = {x} := sorry
  --       "distproj x A = x" FIXME? skipped this second half
-- proof -
--   show "projSet x A = {x}"
--     unfolding projSet_def using assms by auto
--   then show "distproj x A = x"
--     unfolding distproj_def by auto
-- qed

-- lemma distproj_closure [simp]:
--   assumes "x \<in> closure A"
--   shows "distproj x A = x"
-- proof (cases "projSet x A \<noteq> {}")
--   case True
--   show ?thesis
--     using distproj_in_projSet(3)[OF True] assms
--     by (metis closure_empty dist_eq_0_iff distproj_self(2) in_closure_iff_infdist_zero)
-- next
--   case False
--   then show ?thesis unfolding distproj_def by auto
-- qed

-- lemma distproj_le:
--   assumes "y \<in> A"
--   shows "dist x (distproj x A) \<le> dist x y"
-- proof (cases "projSet x A \<noteq> {}")
--   case True
--   show ?thesis using distproj_in_projSet(3)[OF True] infdist_le[OF assms] by auto
-- next
--   case False
--   then show ?thesis unfolding distproj_def by auto
-- qed

lemma projSet_dist_le {x y p : X} {A : Set X} (hy : y ∈ A) (hpx : p ∈ projSet x A) :
    dist x p ≤ dist x y :=
  hpx.2 ▸ infDist_le_dist_of_mem hy
