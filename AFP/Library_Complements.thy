text \<open>The closest point projection of $x$ on $A$. It is not unique, so we choose one point realizing the minimal
distance. And if there is no such point, then we use $x$, to make some statements true without any
assumption.\<close>

definition proj_set::"'a::metric_space \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "proj_set x A = {y \<in> A. dist x y = infdist x A}"

definition distproj::"'a::metric_space \<Rightarrow> 'a set \<Rightarrow> 'a"
  where "distproj x A = (if proj_set x A \<noteq> {} then SOME y. y \<in> proj_set x A else x)"

lemma proj_setD:
  assumes "y \<in> proj_set x A"
  shows "y \<in> A" "dist x y = infdist x A"
using assms unfolding proj_set_def by auto

lemma proj_setI:
  assumes "y \<in> A" "dist x y \<le> infdist x A"
  shows "y \<in> proj_set x A"
using assms infdist_le[OF \<open>y \<in> A\<close>, of x] unfolding proj_set_def by auto

lemma proj_setI':
  assumes "y \<in> A" "\<And>z. z \<in> A \<Longrightarrow> dist x y \<le> dist x z"
  shows "y \<in> proj_set x A"
proof (rule proj_setI[OF \<open>y \<in> A\<close>])
  show "dist x y \<le> infdist x A"
    apply (subst infdist_notempty)
    using assms by (auto intro!: cInf_greatest)
qed

lemma distproj_in_proj_set:
  assumes "proj_set x A \<noteq> {}"
  shows "distproj x A \<in> proj_set x A"
        "distproj x A \<in> A"
        "dist x (distproj x A) = infdist x A"
proof -
  show "distproj x A \<in> proj_set x A"
    using assms unfolding distproj_def using some_in_eq by auto
  then show "distproj x A \<in> A" "dist x (distproj x A) = infdist x A"
    unfolding proj_set_def by auto
qed

lemma proj_set_nonempty_of_proper:
  assumes "proper A" "A \<noteq> {}"
  shows "proj_set x A \<noteq> {}"
proof -
  have "\<exists>y. y \<in> A \<and> dist x y = infdist x A"
    using infdist_proper_attained[OF assms, of x] by auto
  then show "proj_set x A \<noteq> {}" unfolding proj_set_def by auto
qed

lemma distproj_self [simp]:
  assumes "x \<in> A"
  shows "proj_set x A = {x}"
        "distproj x A = x"
proof -
  show "proj_set x A = {x}"
    unfolding proj_set_def using assms by auto
  then show "distproj x A = x"
    unfolding distproj_def by auto
qed

lemma distproj_closure [simp]:
  assumes "x \<in> closure A"
  shows "distproj x A = x"
proof (cases "proj_set x A \<noteq> {}")
  case True
  show ?thesis
    using distproj_in_proj_set(3)[OF True] assms
    by (metis closure_empty dist_eq_0_iff distproj_self(2) in_closure_iff_infdist_zero)
next
  case False
  then show ?thesis unfolding distproj_def by auto
qed

lemma distproj_le:
  assumes "y \<in> A"
  shows "dist x (distproj x A) \<le> dist x y"
proof (cases "proj_set x A \<noteq> {}")
  case True
  show ?thesis using distproj_in_proj_set(3)[OF True] infdist_le[OF assms] by auto
next
  case False
  then show ?thesis unfolding distproj_def by auto
qed

lemma proj_set_dist_le:
  assumes "y \<in> A" "p \<in> proj_set x A"
  shows "dist x p \<le> dist x y"
  using assms infdist_le unfolding proj_set_def by auto
