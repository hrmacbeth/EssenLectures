/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
-/
import Mathlib.Topology.MetricSpace.Isometry

/- # Quasi-isometries -/

variable {X : Type*} [MetricSpace X] {Y : Type*} [MetricSpace Y]

/-- A $(\lambda, C)$ quasi-isometry is a function which behaves like an isometry, up to
an additive error $C$ and a multiplicative error $\lambda$. It can be very different from an
isometry on small scales (for instance, the function integer part is a quasi-isometry between
`ℝ` and `ℤ`), but on large scales it captures many important features of
isometries.

When the space is unbounded, one checks easily that $C \geq 0$ and $\lambda \geq 1$. As this
is the only case of interest (any two bounded sets are quasi-isometric), we incorporate
this requirement in the definition. -/
def quasi_isometry_on (lambda C : ℝ)  (s : Set X) (f : X → Y) : Prop :=
  lambda ≥ 1 ∧ C ≥ 0 ∧ ∀ x ∈ s, ∀ y ∈ s,
    dist (f x) (f y) ≤ lambda * dist x y + C ∧ dist (f x) (f y) ≥ (1/lambda) * dist x y - C

#exit

abbreviation quasi_isometry :: "real \<Rightarrow> real \<Rightarrow> ('a::metric_space \<Rightarrow> 'b::metric_space) \<Rightarrow> bool"
  ("_ _ -quasi'_isometry" [1000, 999])
  where "quasi_isometry lambda C f \<equiv> lambda C-quasi_isometry_on UNIV f"


subsection \<open>Basic properties of quasi-isometries\<close>

lemma quasi_isometry_onD:
  assumes "lambda C-quasi_isometry_on X f"
  shows "∧x y. x ∈ X \<Longrightarrow> y ∈ X \<Longrightarrow> dist (f x) (f y) ≤ lambda * dist x y + C"
        "∧x y. x ∈ X \<Longrightarrow> y ∈ X \<Longrightarrow> dist (f x) (f y) ≥ (1/lambda) * dist x y - C"
        "lambda ≥ 1" "C ≥ 0"
using assms unfolding quasi_isometry_on_def by auto

lemma quasi_isometry_onI [intro]:
  assumes "∧x y. x ∈ X \<Longrightarrow> y ∈ X \<Longrightarrow> dist (f x) (f y) ≤ lambda * dist x y + C"
          "∧x y. x ∈ X \<Longrightarrow> y ∈ X \<Longrightarrow> dist (f x) (f y) ≥ (1/lambda) * dist x y - C"
          "lambda ≥ 1" "C ≥ 0"
  shows "lambda C-quasi_isometry_on X f"
using assms unfolding quasi_isometry_on_def by auto

lemma isometry_quasi_isometry_on:
  assumes "isometry_on X f"
  shows "1 0-quasi_isometry_on X f"
using assms unfolding isometry_on_def quasi_isometry_on_def by auto

lemma quasi_isometry_on_change_params:
  assumes "lambda C-quasi_isometry_on X f" "mu ≥ lambda" "D ≥ C"
  shows "mu D-quasi_isometry_on X f"
proof (rule quasi_isometry_onI)
  have P1: "lambda ≥ 1" "C ≥ 0" using quasi_isometry_onD[OF assms(1)] by auto
  then show P2: "mu ≥ 1" "D ≥ 0" using assms by auto
  fix x y assume inX: "x ∈ X" "y ∈ X"
  have "dist (f x) (f y) ≤ lambda * dist x y + C"
    using quasi_isometry_onD[OF assms(1)] inX by auto
  also have "... ≤ mu * dist x y + D"
    using assms by (auto intro!: mono_intros)
  finally show "dist (f x) (f y) ≤ mu * dist x y + D" by simp
  have "dist (f x) (f y) ≥ (1/lambda) * dist x y - C"
    using quasi_isometry_onD[OF assms(1)] inX by auto
  moreover have "(1/lambda) * dist x y + (- C) ≥ (1/mu) * dist x y + (- D)"
    apply (intro mono_intros)
    using P1 P2 assms by (auto simp add: divide_simps)
  ultimately show "dist (f x) (f y) ≥ (1/mu) * dist x y - D" by simp
qed

lemma quasi_isometry_on_subset:
  assumes "lambda C-quasi_isometry_on X f"
          "Y \<subseteq> X"
  shows "lambda C-quasi_isometry_on Y f"
using assms unfolding quasi_isometry_on_def by auto

lemma quasi_isometry_on_perturb:
  assumes "lambda C-quasi_isometry_on X f"
          "D ≥ 0"
          "∧x. x ∈ X \<Longrightarrow> dist (f x) (g x) ≤ D"
  shows "lambda (C + 2 * D)-quasi_isometry_on X g"
proof (rule quasi_isometry_onI)
  show "lambda ≥ 1" "C + 2 * D ≥ 0" using \<open>D ≥ 0\<close> quasi_isometry_onD[OF assms(1)] by auto
  fix x y assume *: "x ∈ X" "y ∈ X"
  have "dist (g x) (g y) ≤ dist (f x) (f y) + 2 * D"
    using assms(3)[OF *(1)] assms(3)[OF *(2)] dist_triangle4[of "g x" "g y" "f x" "f y"] by (simp add: dist_commute)
  then show "dist (g x) (g y) ≤ lambda * dist x y + (C + 2 * D)"
    using quasi_isometry_onD(1)[OF assms(1) *] by auto
  have "dist (g x) (g y) ≥ dist (f x) (f y) - 2 * D"
    using assms(3)[OF *(1)] assms(3)[OF *(2)] dist_triangle4[of "f x" "f y" "g x" "g y"] by (simp add: dist_commute)
  then show "dist (g x) (g y) ≥ (1/lambda) * dist x y - (C + 2 * D)"
    using quasi_isometry_onD(2)[OF assms(1) *] by auto
qed

lemma quasi_isometry_on_compose:
  assumes "lambda C-quasi_isometry_on X f"
          "mu D-quasi_isometry_on Y g"
          "f`X \<subseteq> Y"
  shows "(lambda * mu) (C * mu + D)-quasi_isometry_on X (g o f)"
proof (rule quasi_isometry_onI)
  have I: "lambda ≥ 1" "C ≥ 0" "mu ≥ 1" "D ≥ 0"
    using quasi_isometry_onD[OF assms(1)] quasi_isometry_onD[OF assms(2)] by auto
  then show "lambda * mu ≥ 1" "C * mu + D ≥ 0"
    by (auto, metis dual_order.order_iff_strict le_numeral_extra(2) mult_le_cancel_right1 order.strict_trans1)
  fix x y assume inX: "x ∈ X" "y ∈ X"
  then have inY: "f x ∈ Y" "f y ∈ Y" using \<open>f`X \<subseteq> Y\<close> by auto
  have "dist ((g o f) x) ((g o f) y) ≤ mu * dist (f x) (f y) + D"
    using quasi_isometry_onD(1)[OF assms(2) inY] by simp
  also have "... ≤ mu * (lambda * dist x y + C) + D"
    using \<open>mu ≥ 1\<close> quasi_isometry_onD(1)[OF assms(1) inX] by auto
  finally show "dist ((g o f) x) ((g o f) y) ≤ (lambda * mu) * dist x y + (C * mu + D)"
    by (auto simp add: algebra_simps)

  have "(1/(lambda * mu)) * dist x y - (C * mu + D) ≤ (1/(lambda * mu)) * dist x y - (C/mu + D)"
    using \<open>mu ≥ 1\<close> \<open>C ≥ 0\<close> apply (auto, auto simp add: divide_simps)
    by (metis eq_iff less_eq_real_def mult.commute mult_eq_0_iff mult_le_cancel_right1 order.trans)
  also have "... = (1/mu) * ((1/lambda) * dist x y - C) - D"
    by (auto simp add: algebra_simps)
  also have "... ≤ (1/mu) * dist (f x) (f y) - D"
    using \<open>mu ≥ 1\<close> quasi_isometry_onD(2)[OF assms(1) inX] by (auto simp add: divide_simps)
  also have "... ≤ dist ((g o f) x) ((g o f) y)"
    using quasi_isometry_onD(2)[OF assms(2) inY] by auto
  finally show "1 / (lambda * mu) * dist x y - (C * mu + D) ≤ dist ((g \<circ> f) x) ((g \<circ> f) y)"
    by auto
qed

lemma quasi_isometry_on_bounded:
  assumes "lambda C-quasi_isometry_on X f"
          "bounded X"
  shows "bounded (f`X)"
proof (cases "X = {}")
  case True
  then show ?thesis by auto
next
  case False
  obtain x where "x ∈ X" using False by auto
  obtain e where e: "∧z. z ∈ X \<Longrightarrow> dist x z ≤ e"
    using bounded_any_center assms(2) by metis
  have "dist (f x) y ≤ C + lambda * e" if "y ∈ f`X" for y
  proof -
    obtain z where *: "z ∈ X" "y = f z" using \<open>y ∈ f`X\<close> by auto
    have "dist (f x) y ≤ lambda * dist x z + C"
      unfolding \<open>y = f z\<close> using * quasi_isometry_onD(1)[OF assms(1) \<open>x ∈ X\<close> \<open>z ∈ X\<close>] by (auto simp add: add_mono)
    also have "... ≤ C + lambda * e" using e[OF \<open>z ∈ X\<close>] quasi_isometry_onD(3)[OF assms(1)] by auto
    finally show ?thesis by simp
  qed
  then show ?thesis unfolding bounded_def by auto
qed

lemma quasi_isometry_on_empty:
  assumes "C ≥ 0" "lambda ≥ 1"
  shows "lambda C-quasi_isometry_on {} f"
using assms unfolding quasi_isometry_on_def by auto

text \<open>Quasi-isometries change the distance to a set by at most $\lambda \cdot + C$, this follows
readily from the fact that this inequality holds pointwise.\<close>

lemma quasi_isometry_on_infdist:
  assumes "lambda C-quasi_isometry_on X f"
          "w ∈ X"
          "S \<subseteq> X"
  shows "infdist (f w) (f`S) ≤ lambda * infdist w S + C"
        "infdist (f w) (f`S) ≥ (1/lambda) * infdist w S - C"
proof -
  have "lambda ≥ 1" "C ≥ 0" using quasi_isometry_onD[OF assms(1)] by auto
  show "infdist (f w) (f`S) ≤ lambda * infdist w S + C"
  proof (cases "S = {}")
    case True
    then show ?thesis
      using \<open>C ≥ 0\<close> unfolding infdist_def by auto
  next
    case False
    then have "(INF x∈S. dist (f w) (f x)) ≤ (INF x∈S. lambda * dist w x + C)"
      apply (rule cINF_superset_mono)
        apply (meson bdd_belowI2 zero_le_dist) using assms by (auto intro!: quasi_isometry_onD(1)[OF assms(1)])
    also have "... = (INF t∈(dist w)`S. lambda * t + C)"
      by (auto simp add: image_comp)
    also have "... = lambda * Inf ((dist w)`S) + C"
      apply (rule continuous_at_Inf_mono[symmetric])
      unfolding mono_def using \<open>lambda ≥ 1\<close> False by (auto intro!: continuous_intros)
    finally show ?thesis unfolding infdist_def using False by (auto simp add: image_comp)
  qed
  show "1 / lambda * infdist w S - C ≤ infdist (f w) (f ` S)"
  proof (cases "S = {}")
    case True
    then show ?thesis
      using \<open>C ≥ 0\<close> unfolding infdist_def by auto
  next
    case False
    then have "(1/lambda) * infdist w S - C = (1/lambda) * Inf ((dist w)`S) - C"
      unfolding infdist_def by auto
    also have "... = (INF t∈(dist w)`S. (1/lambda) * t - C)"
      apply (rule continuous_at_Inf_mono)
      unfolding mono_def using \<open>lambda ≥ 1\<close> False by (auto simp add: divide_simps intro!: continuous_intros)
    also have "... = (INF x∈S. (1/lambda) * dist w x - C)"
      by (auto simp add: image_comp)
    also have "... ≤ (INF x∈S. dist (f w) (f x))"
      apply (rule cINF_superset_mono[OF False]) apply (rule bdd_belowI2[of _ "-C"])
      using assms \<open>lambda ≥ 1\<close> apply simp apply simp apply (rule quasi_isometry_onD(2)[OF assms(1)])
      using assms by auto
    finally show ?thesis unfolding infdist_def using False by (auto simp add: image_comp)
  qed
qed

subsection \<open>Quasi-geodesics\<close>

text \<open>A quasi-geodesic is a quasi-isometric embedding of a real segment into a metric space. As the
embedding need not be continuous, a quasi-geodesic does not have to be compact, nor connected, which
can be a problem. However, in a geodesic space, it is always possible to deform a quasi-geodesic
into a continuous one (at the price of worsening the quasi-isometry constants). This is the content
of the proposition \verb+quasi_geodesic_made_lipschitz+ below, which is a variation around Lemma
III.H.1.11 in~\<^cite>\<open>"bridson_haefliger"\<close>. The strategy of the proof is simple: assume that the
quasi-geodesic $c$ is defined on $[a,b]$. Then, on the points $a$, $a+C/\lambda$, $\cdots$,
$a+ N \cdot C/\lambda$, $b$, take $d$ equal to $c$, where $N$ is chosen so that the distance
between the last point and $b$ is in $[C/\lambda, 2C/\lambda)$. In the intervals, take $d$ to
be geodesic.\<close>
-- **Lemma 2.1**
proposition (in geodesic_space) quasi_geodesic_made_lipschitz:
  fixes c::"real \<Rightarrow> 'a"
  assumes "lambda C-quasi_isometry_on {a..b} c" "dist (c a) (c b) ≥ 2 * C"
  shows "\<exists>d. continuous_on {a..b} d ∧ d a = c a ∧ d b = c b
              ∧ (∀ x∈{a..b}. dist (c x) (d x) ≤ 4 * C)
              ∧ lambda (4 * C)-quasi_isometry_on {a..b} d
              ∧ (2 * lambda)-lipschitz_on {a..b} d
              ∧ hausdorff_distance (c`{a..b}) (d`{a..b}) ≤ 2 * C"
proof -
  consider "C = 0" | "C > 0 ∧ b ≤ a" | "C > 0 ∧ a < b ∧ b ≤ a + 2 * C/lambda" | "C > 0 ∧ a +2 * C/lambda < b"
    using quasi_isometry_onD(4)[OF assms(1)] by fastforce
  then show ?thesis
  proof (cases)
    text \<open>If the original function is Lipschitz, we can use it directly.\<close>
    case 1
    have "lambda-lipschitz_on {a..b} c"
      apply (rule lipschitz_onI) using 1 quasi_isometry_onD[OF assms(1)] by auto
    then have a: "(2 * lambda)-lipschitz_on {a..b} c"
      apply (rule lipschitz_on_mono) using quasi_isometry_onD[OF assms(1)] assms by (auto simp add: divide_simps)
    then have b: "continuous_on {a..b} c"
      using lipschitz_on_continuous_on by blast
    have "continuous_on {a..b} c ∧ c a = c a ∧ c b = c b
                ∧ (∀ x∈{a..b}. dist (c x) (c x) ≤ 4 * C)
                ∧ lambda (4 * C)-quasi_isometry_on {a..b} c
                ∧ (2 * lambda)-lipschitz_on {a..b} c
                ∧ hausdorff_distance (c`{a..b}) (c`{a..b}) ≤ 2 * C"
      using 1 a b assms(1) by auto
    then show ?thesis by blast
  next
    text \<open>If the original interval is empty, anything will do.\<close>
    case 2
    then have "b < a" using assms(2) less_eq_real_def by auto
    then have *: "{a..b} = {}" by auto
    have a: "(2 * lambda)-lipschitz_on {a..b} c"
      unfolding * apply (rule lipschitz_intros) using quasi_isometry_onD[OF assms(1)] assms by (auto simp add: divide_simps)
    then have b: "continuous_on {a..b} c"
      using lipschitz_on_continuous_on by blast
    have "continuous_on {a..b} c ∧ c a = c a ∧ c b = c b
                ∧ (∀ x∈{a..b}. dist (c x) (c x) ≤ 4 * C)
                ∧ lambda (4 * C)-quasi_isometry_on {a..b} c
                ∧ (2 * lambda)-lipschitz_on {a..b} c
                ∧ hausdorff_distance (c`{a..b}) (c`{a..b}) ≤ 2 * C"
      using a b quasi_isometry_on_empty assms(1) quasi_isometry_onD[OF assms(1)] * assms by auto
    then show ?thesis by blast
  next
    text \<open>If the original interval is short, we can use a direct geodesic interpolation between
    its endpoints\<close>
    case 3
    then have C: "C > 0" "lambda ≥ 1" using quasi_isometry_onD[OF assms(1)] by auto
    have [mono_intros]: "1/lambda ≤ lambda" using C by (simp add: divide_simps mult_ge1_powers(1))
    have "a < b" using 3 by simp
    have "2 * C ≤ dist (c a) (c b)" using assms by auto
    also have "... ≤ lambda * dist a b + C"
      using quasi_isometry_onD[OF assms(1)] \<open>a < b\<close> by auto
    also have "... = lambda * (b-a) + C"
      using \<open>a < b\<close> dist_real_def by auto
    finally have *: "C ≤ (b-a) * lambda" by (auto simp add: algebra_simps)
    define d where "d = (\<lambda>x. geodesic_segment_param {(c a)--(c b)} (c a) ((dist (c a) (c b) /(b-a)) * (x-a)))"
    have dend: "d a = c a" "d b = c b" unfolding d_def using \<open>a < b\<close> by auto

    have Lip: "(2 * lambda)-lipschitz_on {a..b} d"
    proof -
      have "(1 * (((2 * lambda)) * (1+0)))-lipschitz_on {a..b} (\<lambda>x. geodesic_segment_param {(c a)--(c b)} (c a) ((dist (c a) (c b) /(b-a)) * (x-a)))"
      proof (rule lipschitz_on_compose2[of _ _ "\<lambda>x. ((dist (c a) (c b) /(b-a)) * (x-a))"], intro lipschitz_intros)
        have "(\<lambda>x. dist (c a) (c b) / (b-a) * (x - a)) ` {a..b} \<subseteq> {0..dist (c a) (c b)}"
          apply auto using \<open>a < b\<close> by (auto simp add: algebra_simps divide_simps intro: mult_right_mono)
        moreover have "1-lipschitz_on {0..dist (c a) (c b)} (geodesic_segment_param {c a--c b} (c a))"
          by (rule isometry_on_lipschitz, simp)
        ultimately show "1-lipschitz_on ((\<lambda>x. dist (c a) (c b) / (b-a) * (x - a)) ` {a..b}) (geodesic_segment_param {c a--c b} (c a))"
          using lipschitz_on_subset by auto

        have "dist (c a) (c b) ≤ lambda * dist a b + C"
          apply (rule quasi_isometry_onD(1)[OF assms(1)])
          using \<open>a < b\<close> by auto
        also have "... = lambda * (b - a) + C"
          unfolding dist_real_def using \<open>a < b\<close> by auto
        also have "... ≤ 2 * lambda * (b-a)"
          using * by (auto simp add: algebra_simps)
        finally show "\<bar>dist (c a) (c b) / (b - a)\<bar> ≤ 2 * lambda"
          using \<open>a < b\<close> by (auto simp add: divide_simps)
      qed
      then show ?thesis unfolding d_def by auto
    qed
    have dist_c_d: "dist (c x) (d x) ≤ 4 * C" if H: "x ∈ {a..b}" for x
    proof -
      have "(x-a) + (b - x) ≤ 2 * C/lambda"
        using that 3 by auto
      then consider "x-a ≤ C/lambda" | "b - x ≤ C/lambda" by linarith
      then have "\<exists>v∈{a,b}. dist x v ≤ C/lambda"
      proof (cases)
        case 1
        show ?thesis
          apply (rule bexI[of _ a]) using 1 H by (auto simp add: dist_real_def)
      next
        case 2
        show ?thesis
          apply (rule bexI[of _ b]) using 2 H by (auto simp add: dist_real_def)
      qed
      then obtain v where v: "v ∈ {a,b}" "dist x v ≤ C/lambda" by auto
      have "dist (c x) (d x) ≤ dist (c x) (c v) + dist (c v) (d v) + dist (d v) (d x)"
        by (intro mono_intros)
      also have "... ≤ (lambda * dist x v + C) + 0 + ((2 * lambda) * dist v x)"
        apply (intro mono_intros quasi_isometry_onD(1)[OF assms(1)] that lipschitz_onD[OF Lip])
        using v \<open>a < b\<close> dend by auto
      also have "... ≤ (lambda * (C/lambda) + C) + 0 + ((2 * lambda) * (C/lambda))"
        apply (intro mono_intros) using C v by (auto simp add: metric_space_class.dist_commute)
      finally show ?thesis
        using C by (auto simp add: algebra_simps divide_simps)
    qed
    text \<open>A similar argument shows that the Hausdorff distance between the images is bounded by $2C$.\<close>
    have "hausdorff_distance (c`{a..b}) (d`{a..b}) ≤ 2 * C"
    proof (rule hausdorff_distanceI2)
      show "0 ≤ 2 * C" using C by auto
      fix z assume "z ∈ c`{a..b}"
      then obtain x where x: "x ∈ {a..b}" "z = c x" by auto
      have "(x-a) + (b - x) ≤ 2 * C/lambda"
        using x 3 by auto
      then consider "x-a ≤ C/lambda" | "b - x ≤ C/lambda" by linarith
      then have "\<exists>v∈{a,b}. dist x v ≤ C/lambda"
      proof (cases)
        case 1
        show ?thesis
          apply (rule bexI[of _ a]) using 1 x by (auto simp add: dist_real_def)
      next
        case 2
        show ?thesis
          apply (rule bexI[of _ b]) using 2 x by (auto simp add: dist_real_def)
      qed
      then obtain v where v: "v ∈ {a,b}" "dist x v ≤ C/lambda" by auto
      have "dist z (d v) = dist (c x) (c v)" unfolding x(2) using v dend by auto
      also have "... ≤ lambda * dist x v + C"
        apply (rule quasi_isometry_onD(1)[OF assms(1)]) using v(1) x(1) by auto
      also have "... ≤ lambda * (C/lambda) + C"
        apply (intro mono_intros) using C v(2) by auto
      also have "... = 2 * C"
        using C by (simp add: divide_simps)
      finally have *: "dist z (d v) ≤ 2 * C" by simp
      show "\<exists>y∈d ` {a..b}. dist z y ≤ 2 * C"
        apply (rule bexI[of _ "d v"]) using * v(1) \<open>a < b\<close> by auto
    next
      fix z assume "z ∈ d`{a..b}"
      then obtain x where x: "x ∈ {a..b}" "z = d x" by auto
      have "(x-a) + (b - x) ≤ 2 * C/lambda"
        using x 3 by auto
      then consider "x-a ≤ C/lambda" | "b - x ≤ C/lambda" by linarith
      then have "\<exists>v∈{a,b}. dist x v ≤ C/lambda"
      proof (cases)
        case 1
        show ?thesis
          apply (rule bexI[of _ a]) using 1 x by (auto simp add: dist_real_def)
      next
        case 2
        show ?thesis
          apply (rule bexI[of _ b]) using 2 x by (auto simp add: dist_real_def)
      qed
      then obtain v where v: "v ∈ {a,b}" "dist x v ≤ C/lambda" by auto
      have "dist z (c v) = dist (d x) (d v)" unfolding x(2) using v dend by auto
      also have "... ≤ 2 * lambda * dist x v"
        apply (rule lipschitz_onD(1)[OF Lip]) using v(1) x(1) by auto
      also have "... ≤ 2 * lambda * (C/lambda)"
        apply (intro mono_intros) using C v(2) by auto
      also have "... = 2 * C"
        using C by (simp add: divide_simps)
      finally have *: "dist z (c v) ≤ 2 * C" by simp
      show "\<exists>y∈c`{a..b}. dist z y ≤ 2 * C"
        apply (rule bexI[of _ "c v"]) using * v(1) \<open>a < b\<close> by auto
    qed
    have "lambda (4 * C)-quasi_isometry_on {a..b} d"
    proof
      show "1 ≤ lambda" using C by auto
      show "0 ≤ 4 * C" using C by auto
      show "dist (d x) (d y) ≤ lambda * dist x y + 4 * C" if "x ∈ {a..b}" "y ∈ {a..b}" for x y
      proof -
        have "dist (d x) (d y) ≤ 2 * lambda * dist x y"
          apply (rule lipschitz_onD[OF Lip]) using that by auto
        also have "... = lambda * dist x y + lambda * dist x y"
          by auto
        also have "... ≤ lambda * dist x y + lambda * (2 * C/lambda)"
          apply (intro mono_intros) using 3 that C unfolding dist_real_def by auto
        also have "... = lambda * dist x y + 2 * C"
          using C by (simp add: algebra_simps divide_simps)
        finally show ?thesis using C by auto
      qed
      show "1 / lambda * dist x y - 4 * C ≤ dist (d x) (d y)" if "x ∈ {a..b}" "y ∈ {a..b}" for x y
      proof -
        have "1/lambda * dist x y - 4 * C ≤ lambda * dist x y - 2 * C"
          apply (intro mono_intros) using C by auto
        also have "... ≤ lambda * (2 * C/lambda) - 2 * C"
          apply (intro mono_intros) using that 3 C unfolding dist_real_def by auto
        also have "... = 0"
          using C by (auto simp add: algebra_simps divide_simps)
        also have "... ≤ dist (d x) (d y)" by auto
        finally show ?thesis by simp
      qed
    qed

    then have "continuous_on {a..b} d ∧ d a = c a ∧ d b = c b
          ∧ lambda (4 * C)-quasi_isometry_on {a..b} d
          ∧ (∀ x∈{a..b}. dist (c x) (d x) ≤ 4 *C)
          ∧ (2*lambda)-lipschitz_on {a..b} d
          ∧ hausdorff_distance (c`{a..b}) (d`{a..b}) ≤ 2 * C"
      using dist_c_d \<open>d a = c a\<close> \<open>d b = c b\<close> \<open>(2*lambda)-lipschitz_on {a..b} d\<close>
            \<open>hausdorff_distance (c`{a..b}) (d`{a..b}) ≤ 2 * C\<close> lipschitz_on_continuous_on by auto
    then show ?thesis by auto
  next
    text \<open>Now, for the only nontrivial case, we use geodesic interpolation between the points
    $a$, $a + C/\lambda$, $\cdots$, $a+N\cdot C/\lambda$, $b'$, $b$ where $N$ is chosen so that
    the distance between $a+N C/\lambda$ and $b$ belongs to $[2C/\lambda, 3C/\lambda)$, and
    $b'$ is the middle of this interval. This gives a decomposition into intervals of length
    at most $3/2\cdot C/\lambda$.\<close>
    case 4
    then have C: "C > 0" "lambda ≥ 1" using quasi_isometry_onD[OF assms(1)] by auto
    have "a < b" using 4 C by (smt divide_pos_pos)

    have [mono_intros]: "1/lambda ≤ lambda" using C by (simp add: divide_simps mult_ge1_powers(1))
    define N where "N = floor((b-a)/(C/lambda)) - 2"
    have N: "N ≤ (b-a)/(C/lambda)-2" "(b-a)/(C/lambda) ≤ N + (3::real)"
      unfolding N_def by linarith+

    have "2 < (b-a)/(C/lambda)"
      using C 4 by (auto simp add: divide_simps algebra_simps)
    then have N0 : "0 ≤ N" unfolding N_def by auto
    define p where "p = (\<lambda>t::int. a + (C/lambda) * t)"
    have pmono: "p i ≤ p j" if "i ≤ j" for i j
      unfolding p_def using that C by (auto simp add: algebra_simps divide_simps)
    have pmono': "p i < p j" if "i < j" for i j
      unfolding p_def using that C by (auto simp add: algebra_simps divide_simps)
    have "p (N+1) ≤ b"
      unfolding p_def using C N by (auto simp add: algebra_simps divide_simps)
    then have pb: "p i ≤ b" if "i ∈ {0..N}" for i
      using that pmono by (meson atLeastAtMost_iff linear not_le order_trans zle_add1_eq_le)
    have bpN: "b - p N ∈ {2 * C/lambda .. 3 * C/lambda}"
      unfolding p_def using C N apply (auto simp add: divide_simps)
      by (auto simp add: algebra_simps)
    have "p N < b" using pmono'[of N "N+1"] \<open>p (N+1) ≤ b\<close> by auto
    define b' where "b' = (b + p N)/2"
    have b': "p N < b'" "b' < b" using \<open>p N < b\<close> unfolding b'_def by auto
    have pb': "p i ≤ b'" if "i ∈ {0..N}" for i
      using pmono[of i N] b' that by auto

    text \<open>Introduce the set $A$ along which one will discretize.\<close>
    define A where "A = p`{0..N} \<union> {b', b}"
    have "finite A" unfolding A_def by auto
    have "b ∈ A" unfolding A_def by auto
    have "p 0 ∈ A" unfolding A_def using \<open>0 ≤ N\<close> by auto
    moreover have pa: "p 0 = a" unfolding p_def by auto
    ultimately have "a ∈ A" by auto
    have "A \<subseteq> {a..b}"
      unfolding A_def using \<open>a < b\<close> b' pa pb pmono N0 by fastforce
    then have "b' ∈ {a..<b}" unfolding A_def using \<open>b' < b\<close> by auto

    have A : "finite A" "A \<subseteq> {a..b}" "a ∈ A" "b ∈ A" "a < b" by fact+

    have nx: "next_in A x = x + C/lambda" if "x ∈ A" "x \<noteq> b" "x \<noteq> b'" "x \<noteq> p N" for x
    proof (rule next_inI[OF A])
      show "x ∈ {a..<b}" using \<open>x ∈ A\<close> \<open>A \<subseteq> {a..b}\<close> \<open>x \<noteq> b\<close> by auto
      obtain i where i: "x = p i" "i ∈ {0..N}"
        using \<open>x ∈ A\<close> \<open>x \<noteq> b\<close> \<open>x \<noteq> b'\<close> unfolding A_def by auto
      have *: "p (i+1) = x + C/lambda" unfolding i(1) p_def by (auto simp add: algebra_simps)
      have "i \<noteq> N" using that i by auto
      then have "i + 1 ∈ {0..N}" using \<open>i ∈ {0..N}\<close> by auto
      then have "p (i+1) ∈ A" unfolding A_def by fastforce
      then show "x + C/lambda ∈ A" unfolding * by auto
      show "x < x + C / lambda" using C by auto
      show "{x<..<x + C / lambda} \<inter> A = {}"
      proof (auto)
        fix y assume y: "y ∈ A" "x < y" "y < x + C/lambda"
        consider "y = b" | "y = b'" | "\<exists>j≤i. y = p j" | "\<exists>j>i. y = p j"
          using \<open>y ∈ A\<close> not_less unfolding A_def by auto
        then show False
        proof (cases)
          case 1
          have "x + C/lambda ≤ b" unfolding *[symmetric] using \<open>i + 1 ∈ {0..N}\<close> pb by auto
          then show False using y(3) unfolding 1 i(1) by auto
        next
          case 2
          have "x + C/lambda ≤ b'" unfolding *[symmetric] using \<open>i + 1 ∈ {0..N}\<close> pb' by auto
          then show False using y(3) unfolding 2 i(1) by auto
        next
          case 3
          then obtain j where j: "j ≤ i" "y = p j" by auto
          have "y ≤ x" unfolding j(2) i(1) using pmono[OF \<open>j ≤ i\<close>] by simp
          then show False using \<open>x < y\<close> by auto
        next
          case 4
          then obtain j where j: "j > i" "y = p j" by auto
          then have "i+1 ≤ j" by auto
          have "x + C/lambda ≤ y" unfolding j(2) *[symmetric] using pmono[OF \<open>i+1 ≤ j\<close>] by auto
          then show False using \<open>y < x + C/lambda\<close> by auto
        qed
      qed
    qed
    have npN: "next_in A (p N) = b'"
    proof (rule next_inI[OF A])
      show "p N ∈ {a..<b}" using pa pmono \<open>0 ≤ N\<close> \<open>p N < b\<close> by auto
      show "p N < b'" by fact
      show "b' ∈ A" unfolding A_def by auto
      show "{p N<..<b'} \<inter> A = {}"
        unfolding A_def using pmono b' by force
    qed
    have nb': "next_in A (b') = b"
    proof (rule next_inI[OF A])
      show "b' ∈ {a..<b}" using A_def A \<open>b' < b\<close> by auto
      show "b' < b" by fact
      show "b ∈ A" by fact
      show "{b'<..<b} \<inter> A = {}"
        unfolding A_def using pmono b' by force
    qed
    have gap: "next_in A x - x ∈ {C/lambda.. 3/2 * C/lambda}" if "x ∈ A - {b}" for x
    proof (cases "x = p N \<or> x = b'")
      case True
      then show ?thesis using npN nb' bpN b'_def by force
    next
      case False
      have *: "next_in A x = x + C/lambda"
        apply (rule nx) using that False by auto
      show ?thesis unfolding * using C by (auto simp add: algebra_simps divide_simps)
    qed

    text \<open>We can now define the function $d$, by geodesic interpolation between points in $A$.\<close>
    define d where "d x = (if x ∈ A then c x
        else geodesic_segment_param {c (prev_in A x) -- c (next_in A x)} (c (prev_in A x))
            ((x - prev_in A x)/(next_in A x - prev_in A x) * dist (c(prev_in A x)) (c(next_in A x))))" for x
    have "d a = c a" "d b = c b" unfolding d_def using \<open>a ∈ A\<close> \<open>b ∈ A\<close> by auto

    text \<open>To prove the Lipschitz continuity, we argue that $d$ is Lipschitz on finitely many intervals,
    that cover the interval $[a,b]$, the intervals between points in $A$.
    There is a formula for $d$ on them (the nontrivial point is that the above formulas for $d$
    match at the boundaries).\<close>

    have *: "d x = geodesic_segment_param {(c u)--(c v)} (c u) ((dist (c u) (c v) /(v-u)) * (x-u))"
      if "u ∈ A - {b}" "v = next_in A u" "x ∈ {u..v}" for x u v
    proof -
      have "u ∈ {a..<b}" using that \<open>A \<subseteq> {a..b}\<close> by fastforce
      have H: "u ∈ A" "v ∈ A" "u < v" "A \<inter> {u<..<v} = {}" using that next_in_basics[OF A \<open>u ∈ {a..<b}\<close>] by auto
      consider "x = u" | "x = v" | "x ∈ {u<..<v}" using \<open>x ∈ {u..v}\<close> by fastforce
      then show ?thesis
      proof (cases)
        case 1
        then have "d x = c u" unfolding d_def using \<open>u ∈ A- {b}\<close> \<open>A \<subseteq> {a..b}\<close> by auto
        then show ?thesis unfolding 1 by auto
      next
        case 2
        then have "d x = c v" unfolding d_def using \<open>v ∈ A\<close> \<open>A \<subseteq> {a..b}\<close> by auto
        then show ?thesis unfolding 2 using \<open>u < v\<close> by auto
      next
        case 3
        have *: "prev_in A x = u"
          apply (rule prev_inI[OF A]) using 3 H \<open>A \<subseteq> {a..b}\<close> by auto
        have **: "next_in A x = v"
          apply (rule next_inI[OF A]) using 3 H \<open>A \<subseteq> {a..b}\<close> by auto
        show ?thesis unfolding d_def * ** using 3 H \<open>A \<inter> {u<..<v} = {}\<close> \<open>A \<subseteq> {a..b}\<close>
          by (auto simp add: algebra_simps)
      qed
    qed

    text \<open>From the above formula, we deduce that $d$ is Lipschitz on those intervals.\<close>
    have lip0: "(lambda + C / (next_in A u - u))-lipschitz_on {u..next_in A u} d" if "u ∈ A - {b}" for u
    proof -
      define v where "v = next_in A u"
      have "u ∈ {a..<b}" using that \<open>A \<subseteq> {a..b}\<close> by fastforce
      have "u ∈ A" "v ∈ A" "u < v" "A \<inter> {u<..<v} = {}"
        unfolding v_def using that next_in_basics[OF A \<open>u ∈ {a..<b}\<close>] by auto

      have "(1 * (((lambda + C / (next_in A u - u))) * (1+0)))-lipschitz_on {u..v} (\<lambda>x. geodesic_segment_param {(c u)--(c v)} (c u) ((dist (c u) (c v) /(v-u)) * (x-u)))"
      proof (rule lipschitz_on_compose2[of _ _ "\<lambda>x. ((dist (c u) (c v) /(v-u)) * (x-u))"], intro lipschitz_intros)
        have "(\<lambda>x. dist (c u) (c v) / (v - u) * (x - u)) ` {u..v} \<subseteq> {0..dist (c u) (c v)}"
          apply auto using \<open>u < v\<close> by (auto simp add: algebra_simps divide_simps intro: mult_right_mono)
        moreover have "1-lipschitz_on {0..dist (c u) (c v)} (geodesic_segment_param {c u--c v} (c u))"
          by (rule isometry_on_lipschitz, simp)
        ultimately show "1-lipschitz_on ((\<lambda>x. dist (c u) (c v) / (v - u) * (x - u)) ` {u..v}) (geodesic_segment_param {c u--c v} (c u))"
          using lipschitz_on_subset by auto

        have "dist (c u) (c v) ≤ lambda * dist u v + C"
          apply (rule quasi_isometry_onD(1)[OF assms(1)])
          using \<open>u ∈ A\<close> \<open>v ∈ A\<close> \<open>A \<subseteq> {a..b}\<close> by auto
        also have "... = lambda * (v - u) + C"
          unfolding dist_real_def using \<open>u < v\<close> by auto
        finally show "\<bar>dist (c u) (c v) / (v - u)\<bar> ≤ lambda + C / (next_in A u - u)"
          using \<open>u < v\<close> unfolding v_def by (auto simp add: divide_simps)
      qed
      then show ?thesis
        using *[OF \<open>u ∈ A -{b}\<close> \<open>v = next_in A u\<close>] unfolding v_def
        by (auto intro: lipschitz_on_transform)
    qed
    have lip: "(2 * lambda)-lipschitz_on {u..next_in A u} d" if "u ∈ A - {b}" for u
    proof (rule lipschitz_on_mono[OF lip0[OF that]], auto)
      define v where "v = next_in A u"
      have "u ∈ {a..<b}" using that \<open>A \<subseteq> {a..b}\<close> by fastforce
      have "u ∈ A" "v ∈ A" "u < v" "A \<inter> {u<..<v} = {}"
        unfolding v_def using that next_in_basics[OF A \<open>u ∈ {a..<b}\<close>] by auto
      have Duv: "v - u ∈ {C/lambda .. 2 * C/lambda}"
        unfolding v_def using gap[OF \<open>u ∈ A - {b}\<close>] by simp
      then show " C / (next_in A u - u) ≤ lambda"
        using \<open>u < v\<close> C unfolding v_def by (auto simp add: algebra_simps divide_simps)
    qed

    text \<open>The Lipschitz continuity of $d$ now follows from its Lipschitz continuity on each
    subinterval in $I$.\<close>
    have Lip: "(2 * lambda)-lipschitz_on {a..b} d"
      apply (rule lipschitz_on_closed_Union[of "{{u..next_in A u} |u. u ∈ A - {b}}" _ "\<lambda>x. x"])
      using lip \<open>finite A\<close> C intervals_decomposition[OF A] using assms by auto
    then have "continuous_on {a..b} d"
      using lipschitz_on_continuous_on by auto

    text \<open>$d$ has good upper controls on each basic interval.\<close>
    have QI0: "dist (d x) (d y) ≤ lambda * dist x y + C"
      if H: "u ∈ A - {b}" "x ∈ {u..next_in A u}" "y ∈ {u..next_in A u}" for u x y
    proof -
      have "u < next_in A u" using H(1) A next_in_basics(2)[OF A] by auto
      moreover have "dist x y ≤ next_in A u - u" unfolding dist_real_def using H by auto
      ultimately have *: "dist x y / (next_in A u - u) ≤ 1" by (simp add: divide_simps)
      have "dist (d x) (d y) ≤ (lambda + C / (next_in A u - u)) * dist x y"
        by (rule lipschitz_onD[OF lip0[OF H(1)] H(2) H(3)])
      also have "... = lambda * dist x y + C * (dist x y / (next_in A u - u))"
        by (simp add: algebra_simps)
      also have "... ≤ lambda * dist x y + C * 1"
        apply (intro mono_intros) using C * by auto
      finally show ?thesis by simp
    qed

    text \<open>We can now show that $c$ and $d$ are pointwise close. This follows from the fact that they
    coincide on $A$ and are well controlled in between (for $c$, this is a consequence of the choice
    of $A$. For $d$, it follows from the fact that it is geodesic in the intervals).\<close>

    have dist_c_d: "dist (c x) (d x) ≤ 4 * C" if "x ∈ {a..b}" for x
    proof -
      obtain u where u: "u ∈ A - {b}" "x ∈ {u..next_in A u}"
        using \<open>x ∈ {a..b}\<close> intervals_decomposition[OF A] by blast
      have "(x-u) + (next_in A u - x) ≤ 2 * C/lambda"
        using gap[OF u(1)] by auto
      then consider "x-u ≤ C/lambda" | "next_in A u - x ≤ C/lambda" by linarith
      then have "\<exists>v∈A. dist x v ≤ C/lambda"
      proof (cases)
        case 1
        show ?thesis
          apply (rule bexI[of _ u]) using 1 u by (auto simp add: dist_real_def)
      next
        case 2
        show ?thesis
          apply (rule bexI[of _ "next_in A u"]) using 2 u A(2)
          by (auto simp add: dist_real_def intro!:next_in_basics[OF A])
      qed
      then obtain v where v: "v ∈ A" "dist x v ≤ C/lambda" by auto
      have "dist (c x) (d x) ≤ dist (c x) (c v) + dist (c v) (d v) + dist (d v) (d x)"
        by (intro mono_intros)
      also have "... ≤ (lambda * dist x v + C) + 0 + ((2 * lambda) * dist v x)"
        apply (intro mono_intros quasi_isometry_onD(1)[OF assms(1)] that lipschitz_onD[OF Lip])
        using A(2) \<open>v ∈ A\<close> apply blast
        using \<open>v ∈ A\<close> d_def apply auto[1]
        using A(2) \<open>v ∈ A\<close> by blast
      also have "... ≤ (lambda * (C/lambda) + C) + 0 + ((2 * lambda) * (C/lambda))"
        apply (intro mono_intros) using v(2) C by (auto simp add: metric_space_class.dist_commute)
      finally show ?thesis
        using C by (auto simp add: algebra_simps divide_simps)
    qed
    text \<open>A similar argument shows that the Hausdorff distance between the images is bounded by $2C$.\<close>
    have "hausdorff_distance (c`{a..b}) (d`{a..b}) ≤ 2 * C"
    proof (rule hausdorff_distanceI2)
      show "0 ≤ 2 * C" using C by auto
      fix z assume "z ∈ c`{a..b}"
      then obtain x where x: "x ∈ {a..b}" "z = c x" by auto
      then obtain u where u: "u ∈ A - {b}" "x ∈ {u..next_in A u}"
        using intervals_decomposition[OF A] by blast
      have "(x-u) + (next_in A u - x) ≤ 2 * C/lambda"
        using gap[OF u(1)] by auto
      then consider "x-u ≤ C/lambda" | "next_in A u - x ≤ C/lambda" by linarith
      then have "\<exists>v∈A. dist x v ≤ C/lambda"
      proof (cases)
        case 1
        show ?thesis
          apply (rule bexI[of _ u]) using 1 u by (auto simp add: dist_real_def)
      next
        case 2
        show ?thesis
          apply (rule bexI[of _ "next_in A u"]) using 2 u A(2)
          by (auto simp add: dist_real_def intro!:next_in_basics[OF A])
      qed
      then obtain v where v: "v ∈ A" "dist x v ≤ C/lambda" by auto
      have "dist z (d v) = dist (c x) (c v)" unfolding x(2) d_def using \<open>v ∈ A\<close> by auto
      also have "... ≤ lambda * dist x v + C"
        apply (rule quasi_isometry_onD(1)[OF assms(1)]) using v(1) A(2) x(1) by auto
      also have "... ≤ lambda * (C/lambda) + C"
        apply (intro mono_intros) using C v(2) by auto
      also have "... = 2 * C"
        using C by (simp add: divide_simps)
      finally have *: "dist z (d v) ≤ 2 * C" by simp
      show "\<exists>y∈d ` {a..b}. dist z y ≤ 2 * C"
        apply (rule bexI[of _ "d v"]) using * v(1) A(2) by auto
    next
      fix z assume "z ∈ d`{a..b}"
      then obtain x where x: "x ∈ {a..b}" "z = d x" by auto
      then obtain u where u: "u ∈ A - {b}" "x ∈ {u..next_in A u}"
        using intervals_decomposition[OF A] by blast
      have "(x-u) + (next_in A u - x) ≤ 2 * C/lambda"
        using gap[OF u(1)] by auto
      then consider "x-u ≤ C/lambda" | "next_in A u - x ≤ C/lambda" by linarith
      then have "\<exists>v∈A. dist x v ≤ C/lambda"
      proof (cases)
        case 1
        show ?thesis
          apply (rule bexI[of _ u]) using 1 u by (auto simp add: dist_real_def)
      next
        case 2
        show ?thesis
          apply (rule bexI[of _ "next_in A u"]) using 2 u A(2)
          by (auto simp add: dist_real_def intro!:next_in_basics[OF A])
      qed
      then obtain v where v: "v ∈ A" "dist x v ≤ C/lambda" by auto
      have "dist z (c v) = dist (d x) (d v)" unfolding x(2) d_def using \<open>v ∈ A\<close> by auto
      also have "... ≤ 2 * lambda * dist x v"
        apply (rule lipschitz_onD(1)[OF Lip]) using v(1) A(2) x(1) by auto
      also have "... ≤ 2 * lambda * (C/lambda)"
        apply (intro mono_intros) using C v(2) by auto
      also have "... = 2 * C"
        using C by (simp add: divide_simps)
      finally have *: "dist z (c v) ≤ 2 * C" by simp
      show "\<exists>y∈c`{a..b}. dist z y ≤ 2 * C"
        apply (rule bexI[of _ "c v"]) using * v(1) A(2) by auto
    qed

    text \<open>From the above controls, we check that $d$ is a quasi-isometry, with explicit constants.\<close>
    have "lambda (4 * C)-quasi_isometry_on {a..b} d"
    proof
      show "1 ≤ lambda" using C by auto
      show "0 ≤ 4 * C" using C by auto
      have I : "dist (d x) (d y) ≤ lambda * dist x y + 4 * C" if H: "x ∈ {a..b}" "y ∈ {a..b}" "x < y" for x y
      proof -
        obtain u where u: "u ∈ A - {b}" "x ∈ {u..next_in A u}"
          using intervals_decomposition[OF A] H(1) by force
        have "u ∈ {a..<b}" using u(1) A by auto
        have "next_in A u ∈ A" using next_in_basics(1)[OF A \<open>u ∈ {a..<b}\<close>] by auto
        obtain v where v: "v ∈ A - {b}" "y ∈ {v..next_in A v}"
          using intervals_decomposition[OF A] H(2) by force
        have "v ∈ {a..<b}" using v(1) A by auto
        have "u < next_in A v" using H(3) u(2) v(2) by auto
        then have "u ≤ v"
          using u(1) next_in_basics(3)[OF A, OF \<open>v ∈ {a..<b}\<close>] by auto
        show ?thesis
        proof (cases "u = v")
          case True
          have "dist (d x) (d y) ≤ lambda * dist x y + C"
            apply (rule QI0[OF u]) using v(2) True by auto
          also have "... ≤ lambda * dist x y + 4 * C"
            using C by auto
          finally show ?thesis by simp
        next
          case False
          then have "u < v" using \<open>u ≤ v\<close> by auto
          then have "next_in A u ≤ v" using v(1) next_in_basics(3)[OF A, OF \<open>u ∈ {a..<b}\<close>] by auto
          have d1: "d (next_in A u) = c (next_in A u)"
            using \<open>next_in A u ∈ A\<close> unfolding d_def by auto
          have d2: "d v = c v"
            using v(1) unfolding d_def by auto
          have "dist (d x) (d y) ≤ dist (d x) (d (next_in A u)) + dist (d (next_in A u)) (d v) + dist (d v) (d y)"
            by (intro mono_intros)
          also have "... ≤ (lambda * dist x (next_in A u) + C) + (lambda * dist (next_in A u) v + C)
                            + (lambda * dist v y + C)"
            apply (intro mono_intros)
              apply (rule QI0[OF u]) using u(2) apply simp
             apply (simp add: d1 d2) apply (rule quasi_isometry_onD(1)[OF assms(1)])
            using \<open>next_in A u ∈ A\<close> \<open>A \<subseteq> {a..b}\<close> apply auto[1]
            using \<open>v ∈ A - {b}\<close> \<open>A \<subseteq> {a..b}\<close> apply auto[1]
            apply (rule QI0[OF v(1)]) using v(2) by auto
          also have "... = lambda * dist x y + 3 * C"
            unfolding dist_real_def
            using \<open>x ∈ {u..next_in A u}\<close> \<open>y ∈ {v..next_in A v}\<close> \<open>x < y\<close> \<open>next_in A u ≤ v\<close>
            by (auto simp add: algebra_simps)
          finally show ?thesis using C by simp
        qed
      qed
      show "dist (d x) (d y) ≤ lambda * dist x y + 4 * C" if H: "x ∈ {a..b}" "y ∈ {a..b}" for x y
      proof -
        consider "x < y" | "x = y" | "x > y" by linarith
        then show ?thesis
        proof (cases)
          case 1
          then show ?thesis using I[OF H(1) H(2) 1] by simp
        next
          case 2
          show ?thesis unfolding 2 using C by auto
        next
          case 3
          show ?thesis using I [OF H(2) H(1) 3] by (simp add: metric_space_class.dist_commute)
        qed
      qed
      text \<open>The lower bound is more tricky. We separate the case where $x$ and $y$ are in the same
      interval, when they are in different nearby intervals, and when they are in different
      separated intervals. The latter case is more difficult. In this case, one of the intervals
      has length $C/\lambda$ and the other one has length at most $3/2\cdot C/\lambda$. There,
      we approximate $dist (d x) (d y)$ by $dist (d u') (d v')$ where $u'$ and $v'$ are suitable
      endpoints of the intervals containing respectively $x$ and $y$. We use the inner endpoint
      (between $x$ and $y$) if the distance between $x$ or $y$ and this point is less than $2/5$
      of the length of the interval, and the outer endpoint otherwise. The reason is that, with
      the outer endpoints, we get right away an upper bound for the distance between $x$ and $y$,
      while this is not the case with the inner endpoints where there is an additional error.
      The equilibrium is reached at proportion $2/5$. \<close>
      have J : "dist (d x) (d y) ≥ (1/lambda) * dist x y - 4 * C" if H: "x ∈ {a..b}" "y ∈ {a..b}" "x < y" for x y
      proof -
        obtain u where u: "u ∈ A - {b}" "x ∈ {u..next_in A u}"
          using intervals_decomposition[OF A] H(1) by force
        have "u ∈ {a..<b}" using u(1) A by auto
        have "next_in A u ∈ A" using next_in_basics(1)[OF A \<open>u ∈ {a..<b}\<close>] by auto
        obtain v where v: "v ∈ A - {b}" "y ∈ {v..next_in A v}"
          using intervals_decomposition[OF A] H(2) by force
        have "v ∈ {a..<b}" using v(1) A by auto
        have "next_in A v ∈ A" using next_in_basics(1)[OF A \<open>v ∈ {a..<b}\<close>] by auto
        have "u < next_in A v" using H(3) u(2) v(2) by auto
        then have "u ≤ v"
          using u(1) next_in_basics(3)[OF A, OF \<open>v ∈ {a..<b}\<close>] by auto
        consider "v = u" | "v = next_in A u" | "v \<noteq> u ∧ v \<noteq> next_in A u" by auto
        then show ?thesis
        proof (cases)
          case 1
          have "(1/lambda) * dist x y - 4 * C ≤ lambda * dist x y - 4 * C"
            apply (intro mono_intros) by auto
          also have "... ≤ lambda * (3/2 * C/lambda) - 3/2 * C"
            apply (intro mono_intros)
            using u(2) v(2) unfolding 1 using C gap[OF u(1)] dist_real_def \<open>x < y\<close> by auto
          also have "... = 0"
            using C by auto
          also have "... ≤ dist (d x) (d y)"
            by auto
          finally show ?thesis by simp
        next
          case 2
          have "dist x y ≤ dist x (next_in A u) + dist v y"
            unfolding 2 by (intro mono_intros)
          also have "... ≤ 3/2 * C/lambda + 3/2 * C/lambda"
            apply (intro mono_intros)
            unfolding dist_real_def using u(2) v(2) gap[OF u(1)] gap[OF v(1)] by auto
          finally have *: "dist x y ≤ 3 * C/lambda" by auto
          have "(1/lambda) * dist x y - 4 * C ≤ lambda * dist x y - 4 * C"
            apply (intro mono_intros) by auto
          also have "... ≤ lambda * (3 * C/lambda) - 3 * C"
            apply (intro mono_intros)
            using * C by auto
          also have "... = 0"
            using C by auto
          also have "... ≤ dist (d x) (d y)"
            by auto
          finally show ?thesis by simp
        next
          case 3
          then have "u < v" using \<open>u ≤ v\<close> by auto
          then have *: "next_in A u < v" using v(1) next_in_basics(3)[OF A \<open>u ∈ {a..<b}\<close>] 3 by auto
          have nu: "next_in A u = u + C/lambda"
          proof (rule nx)
            show "u ∈ A" using u(1) by auto
            show "u \<noteq> b" using u(1) by auto
            show "u \<noteq> b'"
            proof
              assume H: "u = b'"
              have "b < v" using * unfolding H nb' by simp
              then show False using \<open>v ∈ {a..<b}\<close> by auto
            qed
            show "u \<noteq> p N"
            proof
              assume H: "u = p N"
              have "b' < v" using * unfolding H npN by simp
              then have "next_in A b' ≤ v" using next_in_basics(3)[OF A \<open>b' ∈ {a..<b}\<close>] v by force
              then show False unfolding nb' using \<open>v ∈ {a..<b}\<close> by auto
            qed
          qed
          have nv: "next_in A v ≤ v + 3/2 * C/lambda" using gap[OF v(1)] by auto

          have d: "d u = c u" "d (next_in A u) = c (next_in A u)" "d v = c v" "d (next_in A v) = c (next_in A v)"
            using \<open>u ∈ A - {b}\<close> \<open>next_in A u ∈ A\<close> \<open>v ∈ A - {b}\<close> \<open>next_in A v ∈ A\<close> unfolding d_def by auto

          text \<open>The interval containing $x$ has length $C/\lambda$, while the interval containing
          $y$ has length at most $\leq 3/2 C/\lambda$. Therefore, $x$ is at proportion $2/5$ of the inner point
          if $x > u + (3/5) C/\lambda$, and $y$ is at proportion $2/5$ of the inner point if
          $y < v + (2/5) \cdot 3/2 \cdot C/\lambda = v + (3/5)C/\lambda$.\<close>
          consider "x ≤ u + (3/5) * C/lambda ∧ y ≤ v + (3/5) * C/lambda"
                 | "x ≥ u + (3/5) * C/lambda ∧ y ≤ v + (3/5) * C/lambda"
                 | "x ≤ u + (3/5) * C/lambda ∧ y ≥ v + (3/5) * C/lambda"
                 | "x ≥ u + (3/5) * C/lambda ∧ y ≥ v + (3/5) * C/lambda"
            by linarith
          then show ?thesis
          proof (cases)
            case 1
            have "(1/lambda) * dist u v - C ≤ dist (c u) (c v)"
              apply (rule quasi_isometry_onD(2)[OF assms(1)])
              using \<open>u ∈ A - {b}\<close> \<open>v ∈ A - {b}\<close> \<open>A \<subseteq> {a..b}\<close> by auto
            also have "... = dist (d u) (d v)"
              using d by auto
            also have "... ≤ dist (d u) (d x) + dist (d x) (d y) + dist (d y) (d v)"
              by (intro mono_intros)
            also have "... ≤ (2 * lambda * dist u x) + dist (d x) (d y) + (2 * lambda * dist y v)"
              apply (intro mono_intros)
              apply (rule lipschitz_onD[OF lip[OF u(1)]]) using u(2) apply auto[1] using u(2) apply auto[1]
              apply (rule lipschitz_onD[OF lip[OF v(1)]]) using v(2) by auto
            also have "... ≤ (2 * lambda * (3/5 * C/lambda)) + dist (d x) (d y) + (2 * lambda * (3/5 * C/lambda))"
              apply (intro mono_intros)
              unfolding dist_real_def using 1 u v C by auto
            also have "... = 12/5 * C + dist (d x) (d y)"
              using C by (auto simp add: algebra_simps divide_simps)
            finally have *: "(1/lambda) * dist u v ≤ dist (d x) (d y) + 17/5 * C" by auto

            have "(1/lambda) * dist x y ≤ (1/lambda) * (dist u v + dist v y)"
              apply (intro mono_intros)
              unfolding dist_real_def using C u(2) v(2) \<open>x < y\<close> by auto
            also have "... ≤ (1/lambda) * (dist u v + 3/5 * C/lambda)"
              apply (intro mono_intros)
              unfolding dist_real_def using 1 v(2) C by auto
            also have "... = (1/lambda) * dist u v + 3/5 * C * (1/(lambda * lambda))"
              using C by (auto simp add: algebra_simps divide_simps)
            also have "... ≤ (1/lambda) * dist u v + 3/5 * C * 1"
              apply (intro mono_intros)
              using C by (auto simp add: divide_simps algebra_simps mult_ge1_powers(1))
            also have "... ≤ (dist (d x) (d y) + 17/5 * C) + 3/5 * C * 1"
              using * by auto
            finally show ?thesis by auto
          next
            case 2
            have "(1/lambda) * dist (next_in A u) v - C ≤ dist (c (next_in A u)) (c v)"
              apply (rule quasi_isometry_onD(2)[OF assms(1)])
              using \<open>next_in A u ∈ A\<close> \<open>v ∈ A - {b}\<close> \<open>A \<subseteq> {a..b}\<close> by auto
            also have "... = dist (d (next_in A u)) (d v)"
              using d by auto
            also have "... ≤ dist (d (next_in A u)) (d x) + dist (d x) (d y) + dist (d y) (d v)"
              by (intro mono_intros)
            also have "... ≤ (2 * lambda * dist (next_in A u) x) + dist (d x) (d y) + (2 * lambda * dist y v)"
              apply (intro mono_intros)
              apply (rule lipschitz_onD[OF lip[OF u(1)]]) using u(2) apply auto[1] using u(2) apply auto[1]
              apply (rule lipschitz_onD[OF lip[OF v(1)]]) using v(2) by auto
            also have "... ≤ (2 * lambda * (2/5 * C/lambda)) + dist (d x) (d y) + (2 * lambda * (3/5 * C/lambda))"
              apply (intro mono_intros)
              unfolding dist_real_def using 2 u v C nu by auto
            also have "... = 2 * C + dist (d x) (d y)"
              using C by (auto simp add: algebra_simps divide_simps)
            finally have *: "(1/lambda) * dist (next_in A u) v ≤ dist (d x) (d y) + 3 * C" by auto

            have "(1/lambda) * dist x y ≤ (1/lambda) * (dist x (next_in A u) + dist (next_in A u) v + dist v y)"
              apply (intro mono_intros)
              unfolding dist_real_def using C u(2) v(2) \<open>x < y\<close> by auto
            also have "... ≤ (1/lambda) * ((2/5 * C/lambda) + dist (next_in A u) v  + (3/5 * C/lambda))"
              apply (intro mono_intros)
              unfolding dist_real_def using 2 u(2) v(2) C nu by auto
            also have "... = (1/lambda) * dist (next_in A u) v + C * (1/(lambda * lambda))"
              using C by (auto simp add: algebra_simps divide_simps)
            also have "... ≤ (1/lambda) * dist (next_in A u) v + C * 1"
              apply (intro mono_intros)
              using C by (auto simp add: divide_simps algebra_simps mult_ge1_powers(1))
            also have "... ≤ (dist (d x) (d y) + 3 * C) + C * 1"
              using * by auto
            finally show ?thesis by auto
          next
            case 3
            have "(1/lambda) * dist u (next_in A v) - C ≤ dist (c u) (c (next_in A v))"
              apply (rule quasi_isometry_onD(2)[OF assms(1)])
              using \<open>u ∈ A - {b}\<close> \<open>next_in A v ∈ A\<close> \<open>A \<subseteq> {a..b}\<close> by auto
            also have "... = dist (d u) (d (next_in A v))"
              using d by auto
            also have "... ≤ dist (d u) (d x) + dist (d x) (d y) + dist (d y) (d (next_in A v))"
              by (intro mono_intros)
            also have "... ≤ (2 * lambda * dist u x) + dist (d x) (d y) + (2 * lambda * dist y (next_in A v))"
              apply (intro mono_intros)
              apply (rule lipschitz_onD[OF lip[OF u(1)]]) using u(2) apply auto[1] using u(2) apply auto[1]
              apply (rule lipschitz_onD[OF lip[OF v(1)]]) using v(2) by auto
            also have "... ≤ (2 * lambda * (3/5 * C/lambda)) + dist (d x) (d y) + (2 * lambda * (9/10 * C/lambda))"
              apply (intro mono_intros)
              unfolding dist_real_def using 3 u v C nv by auto
            also have "... = 3 * C + dist (d x) (d y)"
              using C by (auto simp add: algebra_simps divide_simps)
            finally have *: "(1/lambda) * dist u (next_in A v) ≤ dist (d x) (d y) + 4 * C" by auto

            have "(1/lambda) * dist x y ≤ (1/lambda) * dist u (next_in A v)"
              apply (intro mono_intros)
              unfolding dist_real_def using C u(2) v(2) \<open>x < y\<close> by auto
            also have "... ≤ dist (d x) (d y) + 4 * C"
              using * by auto
            finally show ?thesis by auto
          next
            case 4
            have "(1/lambda) * dist (next_in A u) (next_in A v) - C ≤ dist (c (next_in A u)) (c (next_in A v))"
              apply (rule quasi_isometry_onD(2)[OF assms(1)])
              using \<open>next_in A u ∈ A\<close> \<open>next_in A v ∈ A\<close> \<open>A \<subseteq> {a..b}\<close> by auto
            also have "... = dist (d (next_in A u)) (d (next_in A v))"
              using d by auto
            also have "... ≤ dist (d (next_in A u)) (d x) + dist (d x) (d y) + dist (d y) (d (next_in A v))"
              by (intro mono_intros)
            also have "... ≤ (2 * lambda * dist (next_in A u) x) + dist (d x) (d y) + (2 * lambda * dist y (next_in A v))"
              apply (intro mono_intros)
              apply (rule lipschitz_onD[OF lip[OF u(1)]]) using u(2) apply auto[1] using u(2) apply auto[1]
              apply (rule lipschitz_onD[OF lip[OF v(1)]]) using v(2) by auto
            also have "... ≤ (2 * lambda * (2/5 * C/lambda)) + dist (d x) (d y) + (2 * lambda * (9/10 * C/lambda))"
              apply (intro mono_intros)
              unfolding dist_real_def using 4 u v C nu nv by auto
            also have "... = 13/5 * C + dist (d x) (d y)"
              using C by (auto simp add: algebra_simps divide_simps)
            finally have *: "(1/lambda) * dist (next_in A u) (next_in A v) ≤ dist (d x) (d y) + 18/5 * C" by auto

            have "(1/lambda) * dist x y ≤ (1/lambda) * (dist x (next_in A u) + dist (next_in A u) (next_in A v))"
              apply (intro mono_intros)
              unfolding dist_real_def using C u(2) v(2) \<open>x < y\<close> by auto
            also have "... ≤ (1/lambda) * ((2/5 *C/lambda) + dist (next_in A u) (next_in A v))"
              apply (intro mono_intros)
              unfolding dist_real_def using 4 u(2) v(2) C nu by auto
            also have "... = (1/lambda) * dist (next_in A u) (next_in A v) + 2/5 * C * (1/(lambda * lambda))"
              using C by (auto simp add: algebra_simps divide_simps)
            also have "... ≤ (1/lambda) * dist (next_in A u) (next_in A v) + 2/5 * C * 1"
              apply (intro mono_intros)
              using C by (auto simp add: divide_simps algebra_simps mult_ge1_powers(1))
            also have "... ≤ (dist (d x) (d y) + 18/5 * C) + 2/5 * C * 1"
              using * by auto
            finally show ?thesis by auto
          qed
        qed
      qed
      show "dist (d x) (d y) ≥ (1/lambda) * dist x y - 4 * C" if H: "x ∈ {a..b}" "y ∈ {a..b}" for x y
      proof -
        consider "x < y" | "x = y" | "x > y" by linarith
        then show ?thesis
        proof (cases)
          case 1
          then show ?thesis using J[OF H(1) H(2) 1] by simp
        next
          case 2
          show ?thesis unfolding 2 using C by auto
        next
          case 3
          show ?thesis using J[OF H(2) H(1) 3] by (simp add: metric_space_class.dist_commute)
        qed
      qed
    qed

    text \<open>We have proved that $d$ has all the properties we wanted.\<close>
    then have "continuous_on {a..b} d ∧ d a = c a ∧ d b = c b
          ∧ lambda (4 * C)-quasi_isometry_on {a..b} d
          ∧ (∀ x∈{a..b}. dist (c x) (d x) ≤ 4 *C)
          ∧ (2*lambda)-lipschitz_on {a..b} d
          ∧ hausdorff_distance (c`{a..b}) (d`{a..b}) ≤ 2 * C"
      using dist_c_d \<open>continuous_on {a..b} d\<close> \<open>d a = c a\<close> \<open>d b = c b\<close> \<open>(2*lambda)-lipschitz_on {a..b} d\<close>
            \<open>hausdorff_distance (c`{a..b}) (d`{a..b}) ≤ 2 * C\<close> by auto
    then show ?thesis by auto
  qed
qed
