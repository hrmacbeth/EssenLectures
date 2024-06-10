/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
-/
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Thickening
import GromovHyperbolicity.Prereqs.ClosestPointProjection

/-! # Geodesic spaces

A geodesic space is a metric space in which any pair of points can be joined by a geodesic segment,
i.e., an isometrically embedded copy of a segment in the real line. Most spaces in geometry are
geodesic. We introduce in this section the corresponding class of metric spaces. First, we study
properties of general geodesic segments in metric spaces. -/

noncomputable section

/-! ## Geodesic segments in general metric spaces -/

open Set Classical

variable {X : Type*} [MetricSpace X]

-- need a concept `IsometryOn` to have an exact match to Isabelle, this is a hack using subtypes
def geodesicSegmentBetween (G : Set X) (x y : X) : Prop :=
  ∃ g : ℝ → X, g 0 = x ∧ g (dist x y) = y ∧ Isometry (g ∘ Subtype.val : Icc 0 (dist x y) → _)
    ∧ G = g '' Icc 0 (dist x y)

def geodesic_segment (G : Set X) : Prop := ∃ x y, geodesicSegmentBetween G x y

/-! We also introduce the parametrization of a geodesic segment. It is convenient to use the
following definition, which guarantees that the point is on `G` even without checking that `G`
is a geodesic segment or that the parameter is in the reasonable range: this shortens some
arguments below. -/
noncomputable def geodesic_segment_param (G : Set X) (x : X) (t : ℝ) : X :=
  if h : ∃ w ∈ G, dist x w = t then
    h.choose
  else if h : G.Nonempty then
    h.choose
  else
    have : Nonempty X := ⟨x⟩
    Classical.ofNonempty

-- lemma geodesicSegmentBetweenI:
--   assumes "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
--   shows "geodesicSegmentBetween G x y"
-- unfolding geodesicSegmentBetween_def apply (rule exI[of _ g]) using assms by auto

-- lemma geodesic_segmentI [intro, simp]:
--   assumes "geodesicSegmentBetween G x y"
--   shows "geodesic_segment G"
-- unfolding geodesic_segment_def using assms by auto

-- lemma geodesic_segmentI2 [intro]:
--   assumes "isometry_on {a..b} g" "a \<le> (b::real)"
--   shows "geodesicSegmentBetween (g`{a..b}) (g a) (g b)"
--         "geodesic_segment (g`{a..b})"
-- proof -
--   define h where "h = (\<lambda>t. g (t+a))"
--   have *: "isometry_on {0..b-a} h"
--     apply (rule isometry_onI)
--     using \<open>isometry_on {a..b} g\<close> \<open>a \<le> b\<close> by (auto simp add: isometry_on_def h_def)
--   have **: "dist (h 0) (h (b-a)) = b-a"
--     using isometry_onD[OF \<open>isometry_on {0..b-a} h\<close>, of 0 "b-a"] \<open>a \<le> b\<close> unfolding dist_real_def by auto
--   have "geodesicSegmentBetween (h`{0..b-a}) (h 0) (h (b-a))"
--     unfolding geodesicSegmentBetween_def apply (rule exI[of _ h]) unfolding ** using * by auto
--   moreover have "g`{a..b} = h`{0..b-a}"
--     unfolding h_def apply (auto simp add: image_iff)
--     by (metis add.commute atLeastAtMost_iff diff_ge_0_iff_ge diff_right_mono le_add_diff_inverse)
--   moreover have "h 0 = g a" "h (b-a) = g b" unfolding h_def by auto
--   ultimately show "geodesicSegmentBetween (g`{a..b}) (g a) (g b)" by auto
--   then show "geodesic_segment (g`{a..b})" unfolding geodesic_segment_def by auto
-- qed

-- lemma geodesic_segmentD:
--   assumes "geodesicSegmentBetween G x y"
--   shows "\<exists>g::(real \<Rightarrow> _). (g t = x \<and> g (t + dist x y) = y \<and> isometry_on {t..t+dist x y} g \<and> G = g`{t..t+dist x y})"
-- proof -
--   obtain h where h: "h 0 = x" "h (dist x y) = y" "isometry_on {0..dist x y} h" "G = h`{0..dist x y}"
--     by (meson \<open>geodesicSegmentBetween G x y\<close> geodesicSegmentBetween_def)
--   have * [simp]: "(\<lambda>x. x - t) ` {t..t + dist x y} = {0..dist x y}" by auto
--   define g where "g = (\<lambda>s. h (s - t))"
--   have "g t = x" "g (t + dist x y) = y" using h assms(1) unfolding g_def by auto
--   moreover have "isometry_on {t..t+dist x y} g"
--     unfolding g_def apply (rule isometry_on_compose[of _ _ h])
--     by (simp add: dist_real_def isometry_on_def, simp add: h(3))
--   moreover have "g` {t..t + dist x y} = G" unfolding g_def h(4) using * by (metis image_image)
--   ultimately show ?thesis by auto
-- qed

@[simp] lemma geodesic_segment_endpoints {G : Set X} {x y : X}
    (hxy : geodesicSegmentBetween G x y) : x ∈ G ∧ y ∈ G ∧ G.Nonempty := by
  sorry
-- using assms unfolding geodesicSegmentBetween_def
--   by (auto, metis atLeastAtMost_iff image_eqI less_eq_real_def zero_le_dist)

-- guessed statement
lemma geodesic_segment_commute {X : Type*} [MetricSpace X] (s : Set X) (x y : X) :
    geodesicSegmentBetween s x y ↔ geodesicSegmentBetween s y x := sorry
-- lemma geodesic_segment_commute:
--   assumes "geodesicSegmentBetween G x y"
--   shows "geodesicSegmentBetween G y x"
-- proof -
--   obtain g::"real\<Rightarrow>'a" where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
--     by (meson \<open>geodesicSegmentBetween G x y\<close> geodesicSegmentBetween_def)
--   define h::"real\<Rightarrow>'a" where "h = (\<lambda>t. g(dist x y-t))"
--   have "(\<lambda>t. dist x y -t)`{0..dist x y} = {0..dist x y}" by auto
--   then have "h`{0..dist x y} = G" unfolding g(4) h_def by (metis image_image)
--   moreover have "h 0 = y" "h (dist x y) = x" unfolding h_def using g by auto
--   moreover have "isometry_on {0..dist x y} h"
--     unfolding h_def apply (rule isometry_on_compose[of _ _ g]) using g(3) by auto
--   ultimately show ?thesis
--     unfolding geodesicSegmentBetween_def by (auto simp add: dist_commute)
-- qed

-- `geodesic_segment_dist`
lemma geodesic_segment_dist {G : Set X} {x y : X} (hGxy : geodesicSegmentBetween G x y) {a : X}
    (haG : a ∈ G) :
    dist x a + dist a y = dist x y := by
  sorry
-- proof -
--   obtain g where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
--     by (meson \<open>geodesicSegmentBetween G x y\<close> geodesicSegmentBetween_def)
--   obtain t where t: "t \<in> {0..dist x y}" "a = g t"
--     using g(4) assms by auto
--   have "dist x a = t" using isometry_onD[OF g(3) _ t(1), of 0]
--     unfolding g(1) dist_real_def t(2) using t(1) by auto
--   moreover have "dist a y = dist x y - t" using isometry_onD[OF g(3) _ t(1), of "dist x y"]
--     unfolding g(2) dist_real_def t(2) using t(1) by (auto simp add: dist_commute)
--   ultimately show ?thesis by auto
-- qed

-- lemma geodesic_segment_dist_unique:
--   assumes "geodesicSegmentBetween G x y" "a \<in> G" "b \<in> G" "dist x a = dist x b"
--   shows "a = b"
-- proof -
--   obtain g where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
--     by (meson \<open>geodesicSegmentBetween G x y\<close> geodesicSegmentBetween_def)
--   obtain ta where ta: "ta \<in> {0..dist x y}" "a = g ta"
--     using g(4) assms by auto
--   have *: "dist x a = ta"
--     unfolding g(1)[symmetric] ta(2) using isometry_onD[OF g(3), of 0 ta]
--     unfolding dist_real_def using ta(1) by auto
--   obtain tb where tb: "tb \<in> {0..dist x y}" "b = g tb"
--     using g(4) assms by auto
--   have "dist x b = tb"
--     unfolding g(1)[symmetric] tb(2) using isometry_onD[OF g(3), of 0 tb]
--     unfolding dist_real_def using tb(1) by auto
--   then have "ta = tb" using * \<open>dist x a = dist x b\<close> by auto
--   then show "a = b" using ta(2) tb(2) by auto
-- qed

-- lemma geodesic_segment_union:
--   assumes "dist x z = dist x y + dist y z"
--           "geodesicSegmentBetween G x y" "geodesicSegmentBetween H y z"
--   shows "geodesicSegmentBetween (G \<union> H) x z"
--         "G \<inter> H = {y}"
-- proof -
--   obtain g where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
--     by (meson \<open>geodesicSegmentBetween G x y\<close> geodesicSegmentBetween_def)
--   obtain h where h: "h (dist x y) = y" "h (dist x z) = z" "isometry_on {dist x y..dist x z} h" "H = h`{dist x y..dist x z}"
--     unfolding \<open>dist x z = dist x y + dist y z\<close>
--     using geodesic_segmentD[OF \<open>geodesicSegmentBetween H y z\<close>, of "dist x y"] by auto
--   define f where "f = (\<lambda>t. if t \<le> dist x y then g t else h t)"
--   have fg: "f t = g t" if "t \<le> dist x y" for t
--     unfolding f_def using that by auto
--   have fh: "f t = h t" if "t \<ge> dist x y" for t
--     unfolding f_def apply (cases "t > dist x y") using that g(2) h(1) by auto

--   have "f 0 = x" "f (dist x z) = z" using fg fh g(1) h(2) assms(1) by auto

--   have "f`{0..dist x z} = f`{0..dist x y} \<union> f`{dist x y..dist x z}"
--     unfolding assms(1) image_Un[symmetric] by (simp add: ivl_disj_un_two_touch(4))
--   moreover have "f`{0..dist x y} = G"
--     unfolding g(4) using fg image_cong by force
--   moreover have "f`{dist x y..dist x z} = H"
--     unfolding h(4) using fh image_cong by force
--   ultimately have "f`{0..dist x z} = G \<union> H" by simp

--   have Ifg: "dist (f s) (f t) = s-t" if "0 \<le> t" "t \<le> s" "s \<le> dist x y" for s t
--     using that fg[of s] fg[of t] isometry_onD[OF g(3), of s t] unfolding dist_real_def by auto
--   have Ifh: "dist (f s) (f t) = s-t" if "dist x y \<le> t" "t \<le> s" "s \<le> dist x z" for s t
--     using that fh[of s] fh[of t] isometry_onD[OF h(3), of s t] unfolding dist_real_def by auto

--   have I: "dist (f s) (f t) = s-t" if "0 \<le> t" "t \<le> s" "s \<le> dist x z" for s t
--   proof -
--     consider "t \<le> dist x y \<and> s \<ge> dist x y" | "s \<le> dist x y" | "t \<ge> dist x y" by fastforce
--     then show ?thesis
--     proof (cases)
--       case 1
--       have "dist (f t) (f s) \<le> dist (f t) (f (dist x y)) + dist (f (dist x y)) (f s)"
--         using dist_triangle by auto
--       also have "... \<le> (dist x y - t) + (s - dist x y)"
--         using that 1 Ifg[of t "dist x y"] Ifh[of "dist x y" s] by (auto simp add: dist_commute intro: mono_intros)
--       finally have *: "dist (f t) (f s) \<le> s - t" by simp

--       have "dist x z \<le> dist (f 0) (f t) + dist (f t) (f s) + dist (f s) (f (dist x z))"
--         unfolding \<open>f 0 = x\<close> \<open>f (dist x z) = z\<close> using dist_triangle4 by auto
--       also have "... \<le> t + dist (f t) (f s) + (dist x z - s)"
--         using that 1 Ifg[of 0 t] Ifh[of s "dist x z"] by (auto simp add: dist_commute intro: mono_intros)
--       finally have "s - t \<le> dist (f t) (f s)" by auto
--       then show "dist (f s) (f t) = s-t" using * dist_commute by auto
--     next
--       case 2
--       then show ?thesis using Ifg that by auto
--     next
--       case 3
--       then show ?thesis using Ifh that by auto
--     qed
--   qed
--   have "isometry_on {0..dist x z} f"
--     unfolding isometry_on_def dist_real_def using I
--     by (auto, metis abs_of_nonneg dist_commute dist_real_def le_cases zero_le_dist)
--   then show "geodesicSegmentBetween (G \<union> H) x z"
--     unfolding geodesicSegmentBetween_def
--     using \<open>f 0 = x\<close> \<open>f (dist x z) = z\<close> \<open>f`{0..dist x z} = G \<union> H\<close> by auto
--   have "G \<inter> H \<subseteq> {y}"
--   proof (auto)
--     fix a assume a: "a \<in> G" "a \<in> H"
--     obtain s where s: "s \<in> {0..dist x y}" "a = g s" using a g(4) by auto
--     obtain t where t: "t \<in> {dist x y..dist x z}" "a = h t" using a h(4) by auto
--     have "a = f s" using fg s by auto
--     moreover have "a = f t" using fh t by auto
--     ultimately have "s = t" using isometry_onD[OF \<open>isometry_on {0..dist x z} f\<close>, of s t] s(1) t(1) by auto
--     then have "s = dist x y" using s t by auto
--     then show "a = y" using s(2) g by auto
--   qed
--   then show "G \<inter> H = {y}" using assms by auto
-- qed

-- lemma geodesic_segment_dist_le:
--   assumes "geodesicSegmentBetween G x y" "a \<in> G" "b \<in> G"
--   shows "dist a b \<le> dist x y"
-- proof -
--   obtain g where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
--     by (meson \<open>geodesicSegmentBetween G x y\<close> geodesicSegmentBetween_def)
--   obtain s t where st: "s \<in> {0..dist x y}" "t \<in> {0..dist x y}" "a = g s" "b = g t"
--     using g(4) assms by auto
--   have "dist a b = abs(s-t)" using isometry_onD[OF g(3) st(1) st(2)]
--     unfolding st(3) st(4) dist_real_def by simp
--   then show "dist a b \<le> dist x y" using st(1) st(2) unfolding dist_real_def by auto
-- qed

lemma geodesic_segment_param1 {G : Set X} {x y : X} (h : geodesicSegmentBetween G x y) :
    geodesic_segment_param G x 0 = x := by
  sorry

lemma geodesic_segment_param2 {G : Set X} {x y : X} (h : geodesicSegmentBetween G x y) :
    geodesic_segment_param G x (dist x y) = y := by
  sorry

lemma geodesic_segment_param3 {G : Set X} {x y : X} (h : geodesicSegmentBetween G x y) {t : ℝ}
    (h' : t ∈ Icc 0 (dist x y)) :
    geodesic_segment_param G x t ∈ G := by
  sorry

lemma geodesic_segment_param4 {G : Set X} {x y : X} (h : geodesicSegmentBetween G x y) :
    Isometry (geodesic_segment_param G x ∘ Subtype.val : Icc (0:ℝ) (dist x y) → _) := by
  sorry

lemma geodesic_segment_param5 {G : Set X} {x y : X} (h : geodesicSegmentBetween G x y) :
    (geodesic_segment_param G x) '' (Icc 0 (dist x y)) = G := by
  sorry

lemma geodesic_segment_param6 {G : Set X} {x y : X} (h : geodesicSegmentBetween G x y) {t : ℝ}
    (h1 : t ∈ Icc 0 (dist x y)) :
    dist x (geodesic_segment_param G x t) = t := by
  sorry

lemma geodesic_segment_param7 {G : Set X} {x y : X} (h : geodesicSegmentBetween G x y) {s t : ℝ}
    (h1 : s ∈ Icc 0 (dist x y)) (h2 : t ∈ Icc 0 (dist x y)) :
    dist (geodesic_segment_param G x s) (geodesic_segment_param G x t) = |s - t| := by
  sorry

lemma geodesic_segment_param8 {G : Set X} {x y : X} (h : geodesicSegmentBetween G x y) {z : X}
    (h1 : z ∈ G) :
    z = geodesic_segment_param G x (dist x z) := by
  sorry

-- lemma geodesic_segment_param [simp]:
--   assumes "geodesicSegmentBetween G x y"
--   shows "geodesic_segment_param G x 0 = x"
--         "geodesic_segment_param G x (dist x y) = y"
--         "t \<in> {0..dist x y} \<Longrightarrow> geodesic_segment_param G x t \<in> G"
--         "isometry_on {0..dist x y} (geodesic_segment_param G x)"
--         "(geodesic_segment_param G x)`{0..dist x y} = G"
--         "t \<in> {0..dist x y} \<Longrightarrow> dist x (geodesic_segment_param G x t) = t"
--         "s \<in> {0..dist x y} \<Longrightarrow> t \<in> {0..dist x y} \<Longrightarrow> dist (geodesic_segment_param G x s) (geodesic_segment_param G x t) = abs(s-t)"
--         "z \<in> G \<Longrightarrow> z = geodesic_segment_param G x (dist x z)"
-- proof -
--   obtain g::"real\<Rightarrow>'a" where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
--     by (meson \<open>geodesicSegmentBetween G x y\<close> geodesicSegmentBetween_def)
--   have *: "g t \<in> G \<and> dist x (g t) = t" if "t \<in> {0..dist x y}" for t
--     using isometry_onD[OF g(3), of 0 t] that g(1) g(4) unfolding dist_real_def by auto
--   have G: "geodesic_segment_param G x t = g t" if "t \<in> {0..dist x y}" for t
--   proof -
--     have A: "geodesic_segment_param G x t \<in> G \<and> dist x (geodesic_segment_param G x t) = t"
--       using *[OF that] unfolding geodesic_segment_param_def apply auto
--       using *[OF that] by (metis (mono_tags, lifting) someI)+
--     obtain s where s: "geodesic_segment_param G x t = g s" "s \<in> {0..dist x y}"
--       using A g(4) by auto
--     have "s = t" using *[OF \<open>s \<in> {0..dist x y}\<close>] A unfolding s(1) by auto
--     then show ?thesis using s by auto
--   qed
--   show "geodesic_segment_param G x 0 = x"
--        "geodesic_segment_param G x (dist x y) = y"
--        "t \<in> {0..dist x y} \<Longrightarrow> geodesic_segment_param G x t \<in> G"
--        "isometry_on {0..dist x y} (geodesic_segment_param G x)"
--        "(geodesic_segment_param G x)`{0..dist x y} = G"
--        "t \<in> {0..dist x y} \<Longrightarrow> dist x (geodesic_segment_param G x t) = t"
--        "s \<in> {0..dist x y} \<Longrightarrow> t \<in> {0..dist x y} \<Longrightarrow> dist (geodesic_segment_param G x s) (geodesic_segment_param G x t) = abs(s-t)"
--        "z \<in> G \<Longrightarrow> z = geodesic_segment_param G x (dist x z)"
--     using G g apply (auto simp add: rev_image_eqI)
--     using G isometry_on_cong * atLeastAtMost_iff apply blast
--     using G isometry_on_cong * atLeastAtMost_iff apply blast
--     by (auto simp add: * dist_real_def isometry_onD)
-- qed

lemma geodesic_segment_param_in_segment {G : Set X} (hG : G.Nonempty) {x : X} {t : ℝ} :
    geodesic_segment_param G x t ∈ G :=
  sorry
-- unfolding geodesic_segment_param_def
-- apply (auto, metis (mono_tags, lifting) someI)
-- using assms some_in_eq by fastforce

lemma geodesic_segment_reverse_param {G : Set X} {x y : X}
    (hxy : geodesicSegmentBetween G x y) {t : ℝ} (ht : t ∈ Icc 0 (dist x y)) :
    geodesic_segment_param G y (dist x y - t) = geodesic_segment_param G x t := by
  sorry
-- proof -
--   have * [simp]: "geodesicSegmentBetween G y x"
--     using geodesic_segment_commute[OF assms(1)] by simp
--   have "geodesic_segment_param G y (dist x y - t) \<in> G"
--     apply (rule geodesic_segment_param(3)[of _ _ x])
--     using assms(2) by (auto simp add: dist_commute)
--   moreover have "dist (geodesic_segment_param G y (dist x y - t)) x = t"
--     using geodesic_segment_param(2)[OF *] geodesic_segment_param(7)[OF *, of "dist x y -t" "dist x y"] assms(2) by (auto simp add: dist_commute)
--   moreover have "geodesic_segment_param G x t \<in> G"
--     apply (rule geodesic_segment_param(3)[OF assms(1)])
--     using assms(2) by auto
--   moreover have "dist (geodesic_segment_param G x t) x = t"
--     using geodesic_segment_param(6)[OF assms] by (simp add: dist_commute)
--   ultimately show ?thesis
--     using geodesic_segment_dist_unique[OF assms(1)] by (simp add: dist_commute)
-- qed

lemma dist_along_geodesic_wrt_endpoint {G : Set X} {x y : X}
    (hxy : geodesicSegmentBetween G x y) {u : X} (hu : u ∈ G) {v : X} (hv : v ∈ G) :
    dist u v = |dist u x - dist v x| := by
  sorry
-- proof -
--   have *: "u = geodesic_segment_param G x (dist x u)" "v = geodesic_segment_param G x (dist x v)"
--     using assms by auto
--   have "dist u v = dist (geodesic_segment_param G x (dist x u)) (geodesic_segment_param G x (dist x v))"
--     using * by auto
--   also have "... = abs(dist x u - dist x v)"
--     apply (rule geodesic_segment_param(7)[OF assms(1)]) using assms apply auto
--     using geodesic_segment_dist_le geodesic_segment_endpoints(1) by blast+
--   finally show ?thesis by (simp add: dist_commute)
-- qed

-- text \<open>One often needs to restrict a geodesic segment to a subsegment. We introduce the tools
-- to express this conveniently.\<close>
-- definition geodesic_subsegment::"('a::metric_space) set \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a set"
--   where "geodesic_subsegment G x s t = G \<inter> {z. dist x z \<ge> s \<and> dist x z \<le> t}"

-- text \<open>A subsegment is always contained in the original segment.\<close>
-- lemma geodesic_subsegment_subset:
--   "geodesic_subsegment G x s t \<subseteq> G"
-- unfolding geodesic_subsegment_def by simp

-- text \<open>A subsegment is indeed a geodesic segment, and its endpoints and parametrization can be
-- expressed in terms of the original segment.\<close>
-- lemma geodesic_subsegment:
--   assumes "geodesicSegmentBetween G x y"
--           "0 \<le> s" "s \<le> t" "t \<le> dist x y"
--   shows "geodesic_subsegment G x s t = (geodesic_segment_param G x)`{s..t}"
--         "geodesicSegmentBetween (geodesic_subsegment G x s t) (geodesic_segment_param G x s) (geodesic_segment_param G x t)"
--         "\<And>u. s \<le> u \<Longrightarrow> u \<le> t \<Longrightarrow> geodesic_segment_param (geodesic_subsegment G x s t) (geodesic_segment_param G x s) (u - s) = geodesic_segment_param G x u"
-- proof -
--   show A: "geodesic_subsegment G x s t = (geodesic_segment_param G x)`{s..t}"
--   proof (auto)
--     fix y assume y: "y \<in> geodesic_subsegment G x s t"
--     have "y = geodesic_segment_param G x (dist x y)"
--       apply (rule geodesic_segment_param(8)[OF assms(1)])
--       using y geodesic_subsegment_subset by force
--     moreover have "dist x y \<ge> s \<and> dist x y \<le> t"
--       using y unfolding geodesic_subsegment_def by auto
--     ultimately show "y \<in> geodesic_segment_param G x ` {s..t}" by auto
--   next
--     fix u assume H: "s \<le> u" "u \<le> t"
--     have *: "dist x (geodesic_segment_param G x u) = u"
--       apply (rule geodesic_segment_param(6)[OF assms(1)]) using H assms by auto
--     show "geodesic_segment_param G x u \<in> geodesic_subsegment G x s t"
--       unfolding geodesic_subsegment_def
--       using geodesic_segment_param_in_segment[OF geodesic_segment_endpoints(3)[OF assms(1)]] by (auto simp add: * H)
--   qed

--   have *: "isometry_on {s..t} (geodesic_segment_param G x)"
--     by (rule isometry_on_subset[of "{0..dist x y}"]) (auto simp add: assms)
--   show B: "geodesicSegmentBetween (geodesic_subsegment G x s t) (geodesic_segment_param G x s) (geodesic_segment_param G x t)"
--     unfolding A apply (rule geodesic_segmentI2) using * assms by auto

--   fix u assume u: "s \<le> u" "u \<le> t"
--   show "geodesic_segment_param (geodesic_subsegment G x s t) (geodesic_segment_param G x s) (u - s) = geodesic_segment_param G x u"
--   proof (rule geodesic_segment_dist_unique[OF B])
--     show "geodesic_segment_param (geodesic_subsegment G x s t) (geodesic_segment_param G x s) (u - s) \<in> geodesic_subsegment G x s t"
--       by (rule geodesic_segment_param_in_segment[OF geodesic_segment_endpoints(3)[OF B]])
--     show "geodesic_segment_param G x u \<in> geodesic_subsegment G x s t"
--       unfolding A using u by auto
--     have "dist (geodesic_segment_param G x s) (geodesic_segment_param (geodesic_subsegment G x s t) (geodesic_segment_param G x s) (u - s)) = u - s"
--       using B assms u by auto
--     moreover have "dist (geodesic_segment_param G x s) (geodesic_segment_param G x u) = u -s"
--       using assms u by auto
--     ultimately show "dist (geodesic_segment_param G x s) (geodesic_segment_param (geodesic_subsegment G x s t) (geodesic_segment_param G x s) (u - s)) =
--         dist (geodesic_segment_param G x s) (geodesic_segment_param G x u)"
--       by simp
--   qed
-- qed

-- text \<open>The parameterizations of a segment and a subsegment sharing an endpoint coincide where defined.\<close>
-- lemma geodesic_segment_subparam:
--   assumes "geodesicSegmentBetween G x z" "geodesicSegmentBetween H x y" "H \<subseteq> G" "t \<in> {0..dist x y}"
--   shows "geodesic_segment_param G x t = geodesic_segment_param H x t"
-- proof -
--   have "geodesic_segment_param H x t \<in> G"
--     using assms(3) geodesic_segment_param(3)[OF assms(2) assms(4)] by auto
--   then have "geodesic_segment_param H x t = geodesic_segment_param G x (dist x (geodesic_segment_param H x t))"
--     using geodesic_segment_param(8)[OF assms(1)] by auto
--   then show ?thesis using geodesic_segment_param(6)[OF assms(2) assms(4)] by auto
-- qed

/-- A segment contains a subsegment between any of its points. -/
lemma geodesic_subsegment_exists {G : Set X} (hG : geodesic_segment G) {x y : X} (hx : x ∈ G) (hy : y ∈ G) :
    ∃ H : Set X, H ⊆ G ∧ geodesicSegmentBetween H x y := by
  sorry
-- proof -
--   obtain a0 b0 where Ga0b0: "geodesicSegmentBetween G a0 b0"
--     using assms(1) unfolding geodesic_segment_def by auto
--   text \<open>Permuting the endpoints if necessary, we can ensure that the first endpoint $a$ is closer
--   to $x$ than $y$.\<close>
--   have "\<exists> a b. geodesicSegmentBetween G a b \<and> dist x a \<le> dist y a"
--   proof (cases "dist x a0 \<le> dist y a0")
--     case True
--     show ?thesis
--       apply (rule exI[of _ a0], rule exI[of _ b0]) using True Ga0b0 by auto
--   next
--     case False
--     show ?thesis
--       apply (rule exI[of _ b0], rule exI[of _ a0])
--       using Ga0b0 geodesic_segment_commute geodesic_segment_dist[OF Ga0b0 \<open>x \<in> G\<close>] geodesic_segment_dist[OF Ga0b0 \<open>y \<in> G\<close>] False
--       by (auto simp add: dist_commute)
--   qed
--   then obtain a b where Gab: "geodesicSegmentBetween G a b" "dist x a \<le> dist y a"
--     by auto
--   have *: "0 \<le> dist x a" "dist x a \<le> dist y a" "dist y a \<le> dist a b"
--     using Gab assms by (meson geodesic_segment_dist_le geodesic_segment_endpoints(1) zero_le_dist)+
--   have **: "x = geodesic_segment_param G a (dist x a)" "y = geodesic_segment_param G a (dist y a)"
--     using Gab \<open>x \<in> G\<close> \<open>y \<in> G\<close> by (metis dist_commute geodesic_segment_param(8))+
--   define H where "H = geodesic_subsegment G a (dist x a) (dist y a)"
--   have "H \<subseteq> G"
--     unfolding H_def by (rule geodesic_subsegment_subset)
--   moreover have "geodesicSegmentBetween H x y"
--     unfolding H_def using geodesic_subsegment(2)[OF Gab(1) *] ** by auto
--   ultimately show ?thesis by auto
-- qed

-- text \<open>A geodesic segment is homeomorphic to an interval.\<close>
-- lemma geodesic_segment_homeo_interval:
--   assumes "geodesicSegmentBetween G x y"
--   shows "{0..dist x y} homeomorphic G"
-- proof -
--   obtain g where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
--     by (meson \<open>geodesicSegmentBetween G x y\<close> geodesicSegmentBetween_def)
--   show ?thesis using isometry_on_homeomorphism(3)[OF g(3)] unfolding g(4) by simp
-- qed

/- Just like an interval, a geodesic segment is compact, connected, path connected, bounded,
closed, nonempty, and proper. -/
lemma geodesic_segment_topology {G : Set X} (h : geodesic_segment G) :
    IsCompact G ∧ IsConnected G ∧ IsPathConnected G ∧ Bornology.IsBounded G ∧ IsClosed G
      ∧ G.Nonempty := by -- original also had "proper G"
  sorry
-- proof -
--   show "compact G"
--     using assms geodesic_segment_homeo_interval homeomorphic_compactness
--     unfolding geodesic_segment_def by force
--   show "path_connected G"
--     using assms is_interval_path_connected geodesic_segment_homeo_interval homeomorphic_path_connectedness
--     unfolding geodesic_segment_def
--     by (metis is_interval_cc)
--   then show "connected G"
--     using path_connected_imp_connected by auto
--   show "bounded G"
--     by (rule compact_imp_bounded, fact)
--   show "closed G"
--     by (rule compact_imp_closed, fact)
--   show "G \<noteq> {}"
--     using assms geodesic_segment_def geodesic_segment_endpoints(3) by auto
--   show "proper G"
--     using proper_of_compact \<open>compact G\<close> by auto
-- qed

-- lemma geodesicSegmentBetween_x_x [simp]:
--   "geodesicSegmentBetween {x} x x"
--   "geodesic_segment {x}"
--   "geodesicSegmentBetween G x x \<longleftrightarrow> G = {x}"
-- proof -
--   show *: "geodesicSegmentBetween {x} x x"
--     unfolding geodesicSegmentBetween_def apply (rule exI[of _ "\<lambda>_. x"]) unfolding isometry_on_def by auto
--   then show "geodesic_segment {x}" by auto
--   show "geodesicSegmentBetween G x x \<longleftrightarrow> G = {x}"
--     using geodesic_segment_dist_le geodesic_segment_endpoints(2) * by fastforce
-- qed

-- lemma geodesic_segment_disconnection:
--   assumes "geodesicSegmentBetween G x y" "z \<in> G"
--   shows "(connected (G - {z})) = (z = x \<or> z = y)"
-- proof -
--   obtain g where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
--     by (meson \<open>geodesicSegmentBetween G x y\<close> geodesicSegmentBetween_def)
--   obtain t where t: "t \<in> {0..dist x y}" "z = g t" using \<open>z \<in> G\<close> g(4) by auto
--   have "({0..dist x y} - {t}) homeomorphic (G - {g t})"
--   proof -
--     have *: "isometry_on ({0..dist x y} - {t}) g"
--       apply (rule isometry_on_subset[OF g(3)]) by auto
--     have "({0..dist x y} - {t}) homeomorphic g`({0..dist x y} - {t})"
--       by (rule isometry_on_homeomorphism(3)[OF *])
--     moreover have "g`({0..dist x y} - {t}) = G - {g t}"
--       unfolding g(4) using isometry_on_injective[OF g(3)] t by (auto simp add: inj_onD)
--     ultimately show ?thesis by auto
--   qed
--   moreover have "connected({0..dist x y} - {t}) = (t = 0 \<or> t = dist x y)"
--     using t(1) by (auto simp add: connected_iff_interval, fastforce)
--   ultimately have "connected (G - {z}) = (t = 0 \<or> t = dist x y)"
--     unfolding \<open>z = g t\<close>[symmetric]using homeomorphic_connectedness by blast
--   moreover have "(t = 0 \<or> t = dist x y) = (z = x \<or> z = y)"
--     using t g apply auto
--     by (metis atLeastAtMost_iff isometry_on_inverse(2) order_refl zero_le_dist)+
--   ultimately show ?thesis by auto
-- qed

-- lemma geodesic_segment_unique_endpoints:
--   assumes "geodesicSegmentBetween G x y"
--           "geodesicSegmentBetween G a b"
--   shows "{x, y} = {a, b}"
-- by (metis geodesic_segment_disconnection assms(1) assms(2) doubleton_eq_iff geodesic_segment_endpoints(1) geodesic_segment_endpoints(2))

-- lemma geodesic_segment_subsegment:
--   assumes "geodesic_segment G" "H \<subseteq> G" "compact H" "connected H" "H \<noteq> {}"
--   shows "geodesic_segment H"
-- proof -
--   obtain x y where "geodesicSegmentBetween G x y"
--     using assms unfolding geodesic_segment_def by auto
--   obtain g where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
--     by (meson \<open>geodesicSegmentBetween G x y\<close> geodesicSegmentBetween_def)
--   define L where "L = (inv_into {0..dist x y} g)`H"
--   have "L \<subseteq> {0..dist x y}"
--     unfolding L_def using isometry_on_inverse[OF \<open>isometry_on {0..dist x y} g\<close>] assms(2) g(4) by auto
--   have "isometry_on G (inv_into {0..dist x y} g)"
--     using isometry_on_inverse[OF \<open>isometry_on {0..dist x y} g\<close>] g(4) by auto
--   then have "isometry_on H (inv_into {0..dist x y} g)"
--     using \<open>H \<subseteq> G\<close> isometry_on_subset by auto
--   then have "H homeomorphic L" unfolding L_def using isometry_on_homeomorphism(3) by auto
--   then have "compact L \<and> connected L"
--     using assms homeomorphic_compactness homeomorphic_connectedness by blast
--   then obtain a b where "L = {a..b}"
--     using connected_compact_interval_1[of L] by auto
--   have "a \<le> b" using \<open>H \<noteq> {}\<close> \<open>L = {a..b}\<close> unfolding L_def by auto
--   then have "0 \<le> a" "b \<le> dist x y" using \<open>L \<subseteq> {0..dist x y}\<close> \<open>L = {a..b}\<close> by auto
--   have *: "H = g`{a..b}"
--     by (metis L_def \<open>L = {a..b}\<close> assms(2) g(4) image_inv_into_cancel)
--   show "geodesic_segment H"
--     unfolding * apply (rule geodesic_segmentI2[OF _ \<open>a \<le> b\<close>])
--     apply (rule isometry_on_subset[OF g(3)]) using \<open>0 \<le> a\<close> \<open>b \<le> dist x y\<close> by auto
-- qed

-- text \<open>The image under an isometry of a geodesic segment is still obviously a geodesic segment.\<close>
-- lemma isometry_preserves_geodesicSegmentBetween:
--   assumes "isometry_on X f"
--           "G \<subseteq> X" "geodesicSegmentBetween G x y"
--   shows "geodesicSegmentBetween (f`G) (f x) (f y)"
-- proof -
--   obtain g where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
--     by (meson \<open>geodesicSegmentBetween G x y\<close> geodesicSegmentBetween_def)
--   then have *: "f`G = (f o g) `{0..dist x y}" "f x = (f o g) 0" "f y = (f o g) (dist x y)"
--     by auto
--   show ?thesis
--     unfolding * apply (intro geodesic_segmentI2(1))
--     unfolding comp_def apply (rule isometry_on_compose[of _ g])
--     using g(3) g(4) assms by (auto intro: isometry_on_subset)
-- qed

-- text \<open>The sum of distances $d(w, x) + d(w, y)$ can be controlled using the distance from $w$
-- to a geodesic segment between $x$ and $y$.\<close>
-- lemma geodesic_segment_distance:
--   assumes "geodesicSegmentBetween G x y"
--   shows "dist w x + dist w y \<le> dist x y + 2 * infdist w G"
-- proof -
--   have "\<exists>z \<in> G. infdist w G = dist w z"
--     apply (rule infdist_proper_attained) using assms by (auto simp add: geodesic_segment_topology)
--   then obtain z where z: "z \<in> G" "infdist w G = dist w z" by auto
--   have "dist w x + dist w y \<le> (dist w z + dist z x) + (dist w z + dist z y)"
--     by (intro mono_intros)
--   also have "... = dist x z + dist z y + 2 * dist w z"
--     by (auto simp add: dist_commute)
--   also have "... = dist x y + 2 * infdist w G"
--     using z(1) assms geodesic_segment_dist unfolding z(2) by auto
--   finally show ?thesis by auto
-- qed

/-- If a point `y` is on a geodesic segment between `x` and its closest projection `p` on a set `A`,
then `p` is also a closest projection of `y`, and the closest projection set of `y` is contained in
that of `x`. -/
lemma proj_set_geodesic_same_basepoint {x y p : X} {A : Set X} (hp : p ∈ proj_set x A) {G : Set X}
    (hG : geodesicSegmentBetween G p x) (hy : y ∈ G) :
    p ∈ proj_set y A := by
  sorry
-- proof (rule proj_setI)
--   show "p \<in> A"
--     using assms proj_setD by auto
--   have *: "dist y p \<le> dist y q" if "q \<in> A" for q
--   proof -
--     have "dist p y + dist y x = dist p x"
--       using assms geodesic_segment_dist by blast
--     also have "... \<le> dist q x"
--       using proj_set_dist_le[OF \<open>q \<in> A\<close> assms(1)] by (simp add: dist_commute)
--     also have "... \<le> dist q y + dist y x"
--       by (intro mono_intros)
--     finally show ?thesis
--       by (simp add: dist_commute)
--   qed
--   have "dist y p \<le> Inf (dist y ` A)"
--     apply (rule cINF_greatest) using \<open>p \<in> A\<close> * by auto
--   then show "dist y p \<le> infdist y A"
--     unfolding infdist_def using \<open>p \<in> A\<close> by auto
-- qed

-- lemma proj_set_subset:
--   assumes "p \<in> proj_set x A" "geodesicSegmentBetween G p x" "y \<in> G"
--   shows "proj_set y A \<subseteq> proj_set x A"
-- proof -
--   have "z \<in> proj_set x A" if "z \<in> proj_set y A" for z
--   proof (rule proj_setI)
--     show "z \<in> A" using that proj_setD by auto
--     have "dist x z \<le> dist x y + dist y z"
--       by (intro mono_intros)
--     also have "... \<le> dist x y + dist y p"
--       using proj_set_dist_le[OF proj_setD(1)[OF \<open>p \<in> proj_set x A\<close>] that] by auto
--     also have "... = dist x p"
--       using assms geodesic_segment_commute geodesic_segment_dist by blast
--     also have "... = infdist x A"
--       using proj_setD(2)[OF assms(1)] by simp
--     finally show "dist x z \<le> infdist x A"
--       by simp
--   qed
--   then show ?thesis by auto
-- qed

lemma proj_set_thickening {p x : X} {Z : Set X} (hp : p ∈ proj_set x Z) {D : ℝ} (hD : 0 ≤ D)
    (hD' : D ≤ dist p x) {G : Set X} (hG : geodesicSegmentBetween G p x) :
    geodesic_segment_param G p D ∈ proj_set (geodesic_segment_param G p D) (Metric.cthickening D Z) := by
  sorry
-- lemma proj_set_thickening:
--   assumes "p \<in> proj_set x Z"
--           "0 \<le> D"
--           "D \<le> dist p x"
--           "geodesicSegmentBetween G p x"
--   shows "geodesic_segment_param G p D \<in> proj_set x (\<Union>z\<in>Z. cball z D)"
-- proof (rule proj_setI')
--   have "dist p (geodesic_segment_param G p D) = D"
--     using geodesic_segment_param(7)[OF assms(4), of 0 D]
--     unfolding geodesic_segment_param(1)[OF assms(4)] using assms by simp
--   then show "geodesic_segment_param G p D \<in> (\<Union>z\<in>Z. cball z D)"
--     using proj_setD(1)[OF \<open>p \<in> proj_set x Z\<close>] by force
--   show "dist x (geodesic_segment_param G p D) \<le> dist x y" if "y \<in> (\<Union>z\<in>Z. cball z D)" for y
--   proof -
--     obtain z where y: "y \<in> cball z D" "z \<in> Z" using \<open>y \<in> (\<Union>z\<in>Z. cball z D)\<close> by auto
--     have "dist (geodesic_segment_param G p D) x + D = dist p x"
--       using geodesic_segment_param(7)[OF assms(4), of D "dist p x"]
--       unfolding geodesic_segment_param(2)[OF assms(4)] using assms by simp
--     also have "... \<le> dist z x"
--       using proj_setD(2)[OF \<open>p \<in> proj_set x Z\<close>] infdist_le[OF \<open>z \<in> Z\<close>, of x] by (simp add: dist_commute)
--     also have "... \<le> dist z y + dist y x"
--       by (intro mono_intros)
--     also have "... \<le> D + dist y x"
--       using y by simp
--     finally show ?thesis by (simp add: dist_commute)
--   qed
-- qed

lemma proj_set_thickening' {p x : X} {Z : Set X} (hp : p ∈ proj_set x Z) {D : ℝ} (hD : 0 ≤ D)
    {E : ℝ} (hDE : D ≤ E) (hE : E ≤ dist p x) {G : Set X} (hG : geodesicSegmentBetween G p x) :
    geodesic_segment_param G p D ∈ proj_set (geodesic_segment_param G p E) (Metric.cthickening D Z) := by
  sorry
-- proof -
--   define H where "H = geodesic_subsegment G p D (dist p x)"
--   have H1: "geodesicSegmentBetween H (geodesic_segment_param G p D) x"
--     apply (subst geodesic_segment_param(2)[OF \<open>geodesicSegmentBetween G p x\<close>, symmetric])
--     unfolding H_def apply (rule geodesic_subsegment(2)) using assms by auto
--   have H2: "geodesic_segment_param G p E \<in> H"
--     unfolding H_def using assms geodesic_subsegment(1) by force
--   have "geodesic_segment_param G p D \<in> proj_set x (\<Union>z\<in>Z. cball z D)"
--     apply (rule proj_set_thickening) using assms by auto
--   then show ?thesis
--     by (rule proj_set_geodesic_same_basepoint[OF _ H1 H2])
-- qed

-- text \<open>It is often convenient to use \emph{one} geodesic between $x$ and $y$, even if it is not unique.
-- We introduce a notation for such a choice of a geodesic, denoted \verb+{x--S--y}+ for such a geodesic
-- that moreover remains in the set $S$. We also enforce
-- the condition \verb+{x--S--y} = {y--S--x}+. When there is no such geodesic, we simply take
-- \verb+{x--S--y} = {x, y}+ for definiteness. It would be even better to enforce that, if
-- $a$ is on \verb+{x--S--y}+, then \verb+{x--S--y}+ is the union of \verb+{x--S--a}+ and \verb+{a--S--y}+, but
-- I do not know if such a choice is always possible -- such a choice of geodesics is
-- called a geodesic bicombing.
-- We also write \verb+{x‒y}+ for \verb+{x--UNIV--y}+.\<close>

-- definition some_geodesicSegmentBetween::"'a::metric_space \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a set" ("(1{_--_--_})")
--   where "some_geodesicSegmentBetween = (SOME f. \<forall> x y S. f x S y = f y S x
--     \<and> (if (\<exists>G. geodesicSegmentBetween G x y \<and> G \<subseteq> S) then (geodesicSegmentBetween (f x S y) x y \<and> (f x S y \<subseteq> S))
--         else f x S y = {x, y}))"

-- abbreviation some_geodesicSegmentBetween_UNIV::"'a::metric_space \<Rightarrow> 'a \<Rightarrow> 'a set" ("(1{_--_})")
--   where "some_geodesicSegmentBetween_UNIV x y \<equiv> {x--UNIV--y}"

/-- We prove that there is such a choice of geodesics, compatible with direction reversal. What
we do is choose arbitrarily a geodesic between `x` and `y` if it exists, and then use the geodesic
between `min x y` and `max x y`, for any total order on the space, to ensure that we get the
same result from `x` to `y` or from `y` to `x`. -/
lemma some_geodesicSegmentBetween_exists (X : Type*) [MetricSpace X]
    [∀ x y : X, ∀ S : Set X, Decidable (∃ G, geodesicSegmentBetween G x y ∧ G ⊆ S)] :
    ∃ f : X → Set X → X → Set X, ∀ x y S, f x S y = f y S x
    ∧  (if (∃ G, geodesicSegmentBetween G x y ∧ G ⊆ S) then
          (geodesicSegmentBetween (f x S y) x y ∧ (f x S y ⊆ S))
        else
          f x S y = {x, y}) :=
  sorry
--   define g::"'a \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a set" where
--     "g = (\<lambda>x S y. if (\<exists>G. geodesicSegmentBetween G x y \<and> G \<subseteq> S) then (SOME G. geodesicSegmentBetween G x y \<and> G \<subseteq> S) else {x, y})"
--   have g1: "geodesicSegmentBetween (g x S y) x y \<and> (g x S y \<subseteq> S)" if "\<exists>G. geodesicSegmentBetween G x y \<and> G \<subseteq> S" for x y S
--     unfolding g_def using someI_ex[OF that] by auto
--   have g2: "g x S y = {x, y}" if "\<not>(\<exists>G. geodesicSegmentBetween G x y \<and> G \<subseteq> S)" for x y S
--     unfolding g_def using that by auto
--   obtain r::"'a rel" where r: "well_order_on UNIV r"
--     using well_order_on by auto
--   have A: "x = y" if "(x, y) \<in> r" "(y, x) \<in> r" for x y
--     using r that unfolding well_order_on_def linear_order_on_def partial_order_on_def antisym_def by auto
--   have B: "(x, y) \<in> r \<or> (y, x) \<in> r" for x y
--     using r unfolding well_order_on_def linear_order_on_def total_on_def partial_order_on_def preorder_on_def refl_on_def by force

--   define f where "f = (\<lambda>x S y. if (x, y) \<in> r then g x S y else g y S x)"
--   have "f x S y = f y S x" for x y S unfolding f_def using r A B by auto
--   moreover have "geodesicSegmentBetween (f x S y) x y \<and> (f x S y \<subseteq> S)" if "\<exists>G. geodesicSegmentBetween G x y \<and> G \<subseteq> S" for x y S
--     unfolding f_def using g1 geodesic_segment_commute that by smt
--   moreover have "f x S y = {x, y}" if "\<not>(\<exists>G. geodesicSegmentBetween G x y \<and> G \<subseteq> S)" for x y S
--     unfolding f_def using g2 that geodesic_segment_commute doubleton_eq_iff by metis
--   ultimately show ?thesis by metis
-- qed

/-- It is often convenient to use \emph{one} geodesic between `x` and `y`, even if it is not unique.
We introduce a notation for such a choice of a geodesic, denoted `{x‒S‒y}` for such a geodesic
that moreover remains in the set `S`. We also enforce
the condition `{x‒S‒y} = {y‒S‒x}`. When there is no such geodesic, we simply take
`{x‒S‒y} = {x, y}` for definiteness. It would be even better to enforce that, if
`a` is on `{x‒S‒y}`, then `{x‒S‒y}` is the union of `{x‒S‒a}` and `{a‒S‒y}` but
I do not know if such a choice is always possible -- such a choice of geodesics is
called a geodesic bicombing.
We also write `{x‒y}` for `{x‒(@Set.univ X)‒y}`. -/
def some_geodesicSegmentBetween {X : Type*} [MetricSpace X]
    [∀ x y : X, ∀ S : Set X, Decidable (∃ G, geodesicSegmentBetween G x y ∧ G ⊆ S)]
    (x y : X) (S : Set X) : Set X :=
  (some_geodesicSegmentBetween_exists X).choose x S y

set_option quotPrecheck false in
notation "{" x "‒" S "‒" y "}" => some_geodesicSegmentBetween x y S

abbrev some_geodesicSegmentBetween_UNIV {X : Type*} [MetricSpace X] (x y : X) : Set X :=
  {x‒(@Set.univ X)‒y}

set_option quotPrecheck false in
notation "{" x "‒" y "}" => some_geodesicSegmentBetween_UNIV x y

-- lemma some_geodesic_commute:
--   "{x--S--y} = {y--S--x}"
-- unfolding some_geodesicSegmentBetween_def by (auto simp add: someI_ex[OF some_geodesicSegmentBetween_exists])

-- lemma some_geodesic_segment_description:
--   "(\<exists>G. geodesicSegmentBetween G x y \<and> G \<subseteq> S) \<Longrightarrow> geodesicSegmentBetween {x--S--y} x y"
--   "(\<not>(\<exists>G. geodesicSegmentBetween G x y \<and> G \<subseteq> S)) \<Longrightarrow> {x--S--y} = {x, y}"
-- unfolding some_geodesicSegmentBetween_def by (simp add: someI_ex[OF some_geodesicSegmentBetween_exists])+

/-! ### Basic topological properties of our chosen set of geodesics. -/

-- lemma some_geodesic_compact [simp]:
--   "compact {x--S--y}"
-- apply (cases "\<exists>G. geodesicSegmentBetween G x y \<and> G \<subseteq> S")
-- using some_geodesic_segment_description[of x y] geodesic_segment_topology[of "{x--S--y}"] geodesic_segment_def apply auto
--   by blast

-- lemma some_geodesic_closed [simp]:
--   "closed {x--S--y}"
-- by (rule compact_imp_closed[OF some_geodesic_compact[of x S y]])

-- lemma some_geodesic_bounded [simp]:
--   "bounded {x--S--y}"
-- by (rule compact_imp_bounded[OF some_geodesic_compact[of x S y]])

@[simp] lemma some_geodesic_endpoints {x y : X} : x ∈ {x‒y} ∧ y ∈ {x‒y} ∧ {x‒y}.Nonempty :=
  sorry
-- apply (cases "\<exists>G. geodesicSegmentBetween G x y \<and> G \<subseteq> S") using some_geodesic_segment_description[of x y S] apply auto
-- apply (cases "\<exists>G. geodesicSegmentBetween G x y \<and> G \<subseteq> S") using some_geodesic_segment_description[of x y S] apply auto
-- apply (cases "\<exists>G. geodesicSegmentBetween G x y \<and> G \<subseteq> S") using geodesic_segment_endpoints(3) by (auto, blast)

-- lemma some_geodesic_subsegment:
--   assumes "H \<subseteq> {x--S--y}" "compact H" "connected H" "H \<noteq> {}"
--   shows "geodesic_segment H"
-- apply (cases "\<exists>G. geodesicSegmentBetween G x y \<and> G \<subseteq> S")
-- using some_geodesic_segment_description[of x y] geodesic_segment_subsegment[OF _ assms] geodesic_segment_def apply auto[1]
-- using some_geodesic_segment_description[of x y] assms
-- by (metis connected_finite_iff_sing finite.emptyI finite.insertI finite_subset geodesicSegmentBetween_x_x(2))

-- lemma some_geodesic_in_subset:
--   assumes "x \<in> S" "y \<in> S"
--   shows "{x--S--y} \<subseteq> S"
-- apply (cases "\<exists>G. geodesicSegmentBetween G x y \<and> G \<subseteq> S")
-- unfolding some_geodesicSegmentBetween_def by (simp add: assms someI_ex[OF some_geodesicSegmentBetween_exists])+

-- lemma some_geodesic_same_endpoints [simp]:
--   "{x--S--x} = {x}"
-- apply (cases "\<exists>G. geodesicSegmentBetween G x x \<and> G \<subseteq> S")
-- apply (meson geodesicSegmentBetween_x_x(3) some_geodesic_segment_description(1))
-- by (simp add: some_geodesic_segment_description(2))

-- subsection \<open>Geodesic subsets\<close>

-- text \<open>A subset is \emph{geodesic} if any two of its points can be joined by a geodesic segment.
-- We prove basic properties of such a subset in this paragraph -- notably connectedness. A basic
-- example is given by convex subsets of vector spaces, as closed segments are geodesic.\<close>

-- definition geodesic_subset::"('a::metric_space) set \<Rightarrow> bool"
--   where "geodesic_subset S = (\<forall>x\<in>S. \<forall>y\<in>S. \<exists>G. geodesicSegmentBetween G x y \<and> G \<subseteq> S)"

-- lemma geodesic_subsetD:
--   assumes "geodesic_subset S" "x \<in> S" "y \<in> S"
--   shows "geodesicSegmentBetween {x--S--y} x y"
-- using assms some_geodesic_segment_description(1) unfolding geodesic_subset_def by blast

-- lemma geodesic_subsetI:
--   assumes "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> \<exists>G. geodesicSegmentBetween G x y \<and> G \<subseteq> S"
--   shows "geodesic_subset S"
-- using assms unfolding geodesic_subset_def by auto

-- lemma geodesic_subset_empty:
--   "geodesic_subset {}"
-- using geodesic_subsetI by auto

-- lemma geodesic_subset_singleton:
--   "geodesic_subset {x}"
-- by (auto intro!: geodesic_subsetI geodesicSegmentBetween_x_x(1))

-- lemma geodesic_subset_path_connected:
--   assumes "geodesic_subset S"
--   shows "path_connected S"
-- proof -
--   have "\<exists>g. path g \<and> path_image g \<subseteq> S \<and> pathstart g = x \<and> pathfinish g = y" if "x \<in> S" "y \<in> S" for x y
--   proof -
--     define G where "G = {x--S--y}"
--     have *: "geodesicSegmentBetween G x y" "G \<subseteq> S" "x \<in> G" "y \<in> G"
--       using assms that by (auto simp add: G_def geodesic_subsetD some_geodesic_in_subset that(1) that(2))
--     then have "path_connected G"
--       using geodesic_segment_topology(3) unfolding geodesic_segment_def by auto
--     then have "\<exists>g. path g \<and> path_image g \<subseteq> G \<and> pathstart g = x \<and> pathfinish g = y"
--       using * unfolding path_connected_def by auto
--     then show ?thesis using \<open>G \<subseteq> S\<close> by auto
--   qed
--   then show ?thesis
--     unfolding path_connected_def by auto
-- qed

-- text \<open>To show that a segment in a normed vector space is geodesic, we will need to use its
-- length parametrization, which is given in the next lemma.\<close>

-- lemma closed_segment_as_isometric_image:
--   "((\<lambda>t. x + (t/dist x y) *\<^sub>R (y - x))`{0..dist x y}) = closed_segment x y"
-- proof (auto simp add: closed_segment_def image_iff)
--   fix t assume H: "0 \<le> t" "t \<le> dist x y"
--   show "\<exists>u. x + (t / dist x y) *\<^sub>R (y - x) = (1 - u) *\<^sub>R x + u *\<^sub>R y \<and> 0 \<le> u \<and> u \<le> 1"
--     apply (rule exI[of _ "t/dist x y"])
--     using H apply (auto simp add: algebra_simps divide_simps)
--     apply (metis add_diff_cancel_left' add_diff_eq add_divide_distrib dist_eq_0_iff scaleR_add_left vector_fraction_eq_iff)
--     done
-- next
--   fix u::real assume H: "0 \<le> u" "u \<le> 1"
--   show "\<exists>t\<in>{0..dist x y}. (1 - u) *\<^sub>R x + u *\<^sub>R y = x + (t / dist x y) *\<^sub>R (y - x)"
--     apply (rule bexI[of _ "u * dist x y"])
--     using H by (auto simp add: algebra_simps mult_left_le_one_le)
-- qed

-- proposition closed_segment_is_geodesic:
--   fixes x y::"'a::real_normed_vector"
--   shows "isometry_on {0..dist x y} (\<lambda>t. x + (t/dist x y) *\<^sub>R (y - x))"
--         "geodesicSegmentBetween (closed_segment x y) x y"
--         "geodesic_segment (closed_segment x y)"
-- proof -
--   show *: "isometry_on {0..dist x y} (\<lambda>t. x + (t/dist x y) *\<^sub>R (y - x))"
--     unfolding isometry_on_def dist_norm
--     apply (cases "x = y")
--     by (auto simp add: scaleR_diff_left[symmetric] diff_divide_distrib[symmetric] norm_minus_commute)
--   show "geodesicSegmentBetween (closed_segment x y) x y"
--     unfolding closed_segment_as_isometric_image[symmetric]
--     apply (rule geodesicSegmentBetweenI[OF _ _ *]) by auto
--   then show "geodesic_segment (closed_segment x y)"
--     by auto
-- qed

-- text \<open>We deduce that a convex set is geodesic.\<close>

-- proposition convex_is_geodesic:
--   assumes "convex (S::'a::real_normed_vector set)"
--   shows "geodesic_subset S"
-- proof (rule geodesic_subsetI)
--   fix x y assume H: "x \<in> S" "y \<in> S"
--   show "\<exists>G. geodesicSegmentBetween G x y \<and> G \<subseteq> S"
--     apply (rule exI[of _ "closed_segment x y"])
--     apply (auto simp add: closed_segment_is_geodesic)
--     using H assms convex_contains_segment by blast
-- qed


/- ! ## Geodesic spaces

In this subsection, we define geodesic spaces (metric spaces in which there is a geodesic
segment joining any pair of points). We specialize the previous statements on geodesic segments to
these situations. -/

class GeodesicSpace (X : Type*) [MetricSpace X]

-- class geodesic_space = metric_space +
--   assumes geodesic: "geodesic_subset (UNIV::('a::metric_space) set)"

/- The simplest example of a geodesic space is a real normed vector space. Significant examples
also include graphs (with the graph distance), Riemannian manifolds, and $CAT(\kappa)$ spaces. -/

-- instance real_normed_vector \<subseteq> geodesic_space
-- by (standard, simp add: convex_is_geodesic)

variable [GeodesicSpace X]

@[simp] lemma some_geodesic_is_geodesic_segment (x y : X) :
    geodesicSegmentBetween {x‒y} x y ∧ geodesic_segment {x‒y} := by
  sorry
-- using some_geodesic_segment_description(1)[of x y] geodesic_subsetD[OF geodesic] by (auto, blast)

-- lemma (in geodesic_space) some_geodesic_connected [simp]:
--   "connected {x‒y}" "path_connected {x‒y}"
-- by (auto intro!: geodesic_segment_topology)

/-! In geodesic spaces, we restate as simp rules all properties of the geodesic segment
parametrizations. -/

-- FIXME? in Isabelle these were all marked [simp]

lemma geodesic_segment_param_in_geodesic_spaces1 {x y : X} :
    geodesic_segment_param {x‒y} x 0 = x :=
  sorry

lemma geodesic_segment_param_in_geodesic_spaces2 {x y : X} :
    geodesic_segment_param {x‒y} x (dist x y) = y :=
  sorry

lemma geodesic_segment_param_in_geodesic_spaces3 {x y : X} {t : ℝ} (ht : t ∈ Icc 0 (dist x y)) :
    geodesic_segment_param {x‒y} x t ∈ {x‒y} :=
  sorry

lemma geodesic_segment_param_in_geodesic_spaces4 {x y : X} :
    Isometry (geodesic_segment_param {x‒y} x ∘ Subtype.val : Icc (0:ℝ) (dist x y) → _) := by
  sorry

lemma geodesic_segment_param_in_geodesic_spaces5 {x y : X} :
    (geodesic_segment_param {x‒y} x) '' Icc 0 (dist x y) = {x‒y} :=
  sorry

lemma geodesic_segment_param_in_geodesic_spaces6 {x y : X} {t : ℝ} (ht : t ∈ Icc 0 (dist x y)) :
    dist x (geodesic_segment_param {x‒y} x t) = t :=
  sorry

lemma geodesic_segment_param_in_geodesic_spaces7 {x y : X} {s t : ℝ}
    (hs : s ∈ Icc 0 (dist x y)) (ht : t ∈ Icc 0 (dist x y)) :
    dist (geodesic_segment_param {x‒y} x s) (geodesic_segment_param {x‒y} x t) = |s-t| :=
  sorry

lemma geodesic_segment_param_in_geodesic_spaces8 {x y z : X} (hz : z ∈ {x‒y}) :
    z = geodesic_segment_param {x‒y} x (dist x z) :=
  sorry

-- using geodesic_segment_param[OF some_geodesic_is_geodesic_segment(1)[of x y]] by auto

#exit

subsection \<open>Uniquely geodesic spaces\<close>

text \<open>In this subsection, we define uniquely geodesic spaces, i.e., geodesic spaces in which,
additionally, there is a unique geodesic between any pair of points.\<close>

class uniquely_geodesic_space = geodesic_space +
  assumes uniquely_geodesic: "\<And>x y G H. geodesicSegmentBetween G x y \<Longrightarrow> geodesicSegmentBetween H x y \<Longrightarrow> G = H"

text \<open>To prove that a geodesic space is uniquely geodesic, it suffices to show that there is no loop,
i.e., if two geodesic segments intersect only at their endpoints, then they coincide.

Indeed, assume this holds, and consider two geodesics with the same endpoints. If they differ at
some time $t$, then consider the last time $a$ before $t$ where they coincide, and the first time
$b$ after $t$ where they coincide. Then the restrictions of the two geodesics to $[a,b]$ give
a loop, and a contradiction.\<close>

lemma (in geodesic_space) uniquely_geodesic_spaceI:
  assumes "\<And>G H x (y::'a). geodesicSegmentBetween G x y \<Longrightarrow> geodesicSegmentBetween H x y \<Longrightarrow> G \<inter> H = {x, y} \<Longrightarrow> x = y"
          "geodesicSegmentBetween G x y" "geodesicSegmentBetween H x (y::'a)"
  shows "G = H"
proof -
  obtain g where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
    by (meson \<open>geodesicSegmentBetween G x y\<close> geodesicSegmentBetween_def)
  obtain h where h: "h 0 = x" "h (dist x y) = y" "isometry_on {0..dist x y} h" "H = h`{0..dist x y}"
    by (meson \<open>geodesicSegmentBetween H x y\<close> geodesicSegmentBetween_def)
  have "g t = h t" if "t \<in> {0..dist x y}" for t
  proof (rule ccontr)
    assume "g t \<noteq> h t"
    define Z where "Z = {s \<in> {0..dist x y}. g s = h s}"
    have "0 \<in> Z" "dist x y \<in> Z" unfolding Z_def using g h by auto
    have "t \<notin> Z" unfolding Z_def using \<open>g t \<noteq> h t\<close> by auto
    have [simp]: "closed Z"
    proof -
      have *: "Z = (\<lambda>s. dist (g s) (h s))-`{0} \<inter> {0..dist x y}"
        unfolding Z_def by auto
      show ?thesis
        unfolding * apply (rule closed_vimage_Int)
        using isometry_on_continuous[OF g(3)] isometry_on_continuous[OF h(3)] continuous_on_dist by auto
    qed
    define a where "a = Sup (Z \<inter> {0..t})"
    have a: "a \<in> Z \<inter> {0..t}"
      unfolding a_def apply (rule closed_contains_Sup, auto)
      using \<open>0 \<in> Z\<close> that by auto
    then have "h a = g a" unfolding Z_def by auto
    define b where "b = Inf (Z \<inter> {t..dist x y})"
    have b: "b \<in> Z \<inter> {t..dist x y}"
      unfolding b_def apply (rule closed_contains_Inf, auto)
      using \<open>dist x y \<in> Z\<close> that by auto
    then have "h b = g b" unfolding Z_def by auto
    have notZ: "s \<notin> Z" if "s \<in> {a<..<b}" for s
    proof (rule ccontr, auto, cases "s \<le> t")
      case True
      assume "s \<in> Z"
      then have *: "s \<in> Z \<inter> {0..t}" using that a True by auto
      have "s \<le> a" unfolding a_def apply (rule cSup_upper) using * by auto
      then show False using that by auto
    next
      case False
      assume "s \<in> Z"
      then have *: "s \<in> Z \<inter> {t..dist x y}" using that b False by auto
      have "s \<ge> b" unfolding b_def apply (rule cInf_lower) using * by auto
      then show False using that by auto
    qed
    have "t \<in> {a<..<b}" using a b \<open>t \<notin> Z\<close> less_eq_real_def by auto
    then have "a \<le> b" by auto
    then have "dist (h a) (h b) = b-a"
      using isometry_onD[OF h(3), of a b] a b that unfolding dist_real_def by auto
    then have "dist (h a) (h b) > 0" using \<open>t \<in> {a<..<b}\<close> by auto
    then have "h a \<noteq> h b" by auto

    define G2 where "G2 = g`{a..b}"
    define H2 where "H2 = h`{a..b}"
    have "G2 \<inter> H2 \<subseteq> {h a, h b}"
    proof
      fix z assume z: "z \<in> G2 \<inter> H2"
      obtain sg where sg: "z = g sg" "sg \<in> {a..b}" using z unfolding G2_def by auto
      obtain sh where sh: "z = h sh" "sh \<in> {a..b}" using z unfolding H2_def by auto
      have "sg = dist x z"
        using isometry_onD[OF g(3), of 0 sg] a b sg(2) unfolding sg(1) g(1)[symmetric] dist_real_def by auto
      moreover have "sh = dist x z"
        using isometry_onD[OF h(3), of 0 sh] a b sh(2) unfolding sh(1) h(1)[symmetric] dist_real_def by auto
      ultimately have "sg = sh" by auto
      then have "sh \<in> Z" using sg(1) sh(1) a b sh(2) unfolding Z_def by auto
      then have "sh \<in> {a, b}" using notZ sh(2)
        by (metis IntD2 atLeastAtMost_iff atLeastAtMost_singleton greaterThanLessThan_iff inf_bot_left insertI2 insert_inter_insert not_le)
      then show "z \<in> {h a, h b}" using sh(1) by auto
    qed
    then have "G2 \<inter> H2 = {h a, h b}"
      using \<open>h a = g a\<close> \<open>h b = g b\<close> \<open>a \<le> b\<close> unfolding H2_def G2_def apply auto
      unfolding \<open>h a = g a\<close>[symmetric] \<open>h b = g b\<close>[symmetric] by auto
    moreover have "geodesicSegmentBetween G2 (h a) (h b)"
      unfolding G2_def \<open>h a = g a\<close> \<open>h b = g b\<close>
      apply (rule geodesic_segmentI2) apply (rule isometry_on_subset[OF g(3)])
      using a b that by auto
    moreover have "geodesicSegmentBetween H2 (h a) (h b)"
      unfolding H2_def apply (rule geodesic_segmentI2) apply (rule isometry_on_subset[OF h(3)])
      using a b that by auto
    ultimately have "h a = h b" using assms(1) by auto
    then show False using \<open>h a \<noteq> h b\<close> by simp
  qed
  then show "G = H" using g(4) h(4) by (simp add: image_def)
qed

context uniquely_geodesic_space
begin

lemma geodesic_segment_unique:
  "geodesicSegmentBetween G x y = (G = {x--(y::'a)})"
using uniquely_geodesic[of _ x y] by (meson some_geodesic_is_geodesic_segment)

lemma geodesic_segment_dist':
  assumes "dist x z = dist x y + dist y z"
  shows "y \<in> {x--z}" "{x--z} = {x‒y} \<union> {y--z}"
proof -
  have "geodesicSegmentBetween ({x‒y} \<union> {y--z}) x z"
    using geodesic_segment_union[OF assms] by auto
  then show "{x--z} = {x‒y} \<union> {y--z}"
    using geodesic_segment_unique by auto
  then show "y \<in> {x--z}" by auto
qed

lemma geodesic_segment_expression:
  "{x--z} = {y. dist x z = dist x y + dist y z}"
using geodesic_segment_dist'(1) geodesic_segment_dist[OF some_geodesic_is_geodesic_segment(1)] by auto

lemma geodesic_segment_split:
  assumes "(y::'a) \<in> {x--z}"
  shows "{x--z} = {x‒y} \<union> {y--z}"
        "{x‒y} \<inter> {y--z} = {y}"
apply (metis assms geodesic_segment_dist geodesic_segment_dist'(2) some_geodesic_is_geodesic_segment(1))
apply (rule geodesic_segment_union(2)[of x z], auto simp add: assms)
using assms geodesic_segment_expression by blast

lemma geodesic_segment_subparam':
  assumes "y \<in> {x--z}" "t \<in> {0..dist x y}"
  shows "geodesic_segment_param {x--z} x t = geodesic_segment_param {x‒y} x t"
apply (rule geodesic_segment_subparam[of _ _ z _ y]) using assms apply auto
using geodesic_segment_split(1)[OF assms(1)] by auto

end (*of context uniquely_geodesic_space*)


subsection \<open>A complete metric space with middles is geodesic.\<close>

text \<open>A complete space in which every pair of points has a middle (i.e., a point $m$ which
is half distance of $x$ and $y$) is geodesic: to construct a geodesic between $x_0$
and $y_0$, first choose a middle $m$, then middles of the pairs $(x_0,m)$ and $(m, y_0)$, and so
on. This will define the geodesic on dyadic points (and this is indeed an isometry on these dyadic
points. Then, extend it by uniform continuity to the whole segment $[0, dist x0 y0]$.

The formal proof will be done in a locale where $x_0$ and $y_0$ are fixed, for notational simplicity.
We define inductively the sequence of middles, in a function \verb+geod+ of two natural variables:
$geod n m$ corresponds to the image of the dyadic point $m/2^n$. It is defined inductively, by
$geod (n+1) (2m) = geod n m$, and $geod (n+1) (2m+1)$ is a middle of $geod n m$ and $geod n (m+1)$.
This is not a completely classical inductive definition, so one has to use \verb+function+ to define
it. Then, one checks inductively that it has all the properties we want, and use it to define the
geodesic segment on dyadic points. We will not use a canonical
representative for a dyadic point, but any representative (i.e., numerator and denominator
will not have to be coprime) -- this will not create problems as $geod$ does not depend on the choice
of the representative, by construction.\<close>

locale complete_space_with_middle =
  fixes x0 y0::"'a::complete_space"
  assumes middles: "\<And>x y::'a. \<exists>z. dist x z = (dist x y)/2 \<and> dist z y = (dist x y)/2"
begin

definition middle::"'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "middle x y = (SOME z. dist x z = (dist x y)/2 \<and> dist z y = (dist x y)/2)"

lemma middle:
  "dist x (middle x y) = (dist x y)/2"
  "dist (middle x y) y = (dist x y)/2"
unfolding middle_def using middles[of x y] by (metis (mono_tags, lifting) someI_ex)+

function geod::"nat \<Rightarrow> nat \<Rightarrow> 'a" where
 "geod 0 0 = x0"
|"geod 0 (Suc m) = y0"
|"geod (Suc n) (2 * m) = geod n m"
|"geod (Suc n) (Suc (2*m)) = middle (geod n m) (geod n (Suc m))"
apply (auto simp add: double_not_eq_Suc_double)
by (metis One_nat_def dvd_mult_div_cancel list_decode.cases odd_Suc_minus_one odd_two_times_div_two_nat)
termination by lexicographic_order

text \<open>By induction, the distance between successive points is $D/2^n$.\<close>

lemma geod_distance_successor:
  "\<forall>a < 2^n. dist (geod n a) (geod n (Suc a)) = dist x0 y0 / 2^n"
proof (induction n)
  case 0
  show ?case by auto
next
  case (Suc n)
  show ?case
  proof (auto)
    fix a::nat assume a: "a < 2 * 2^n"
    obtain m where m: "a = 2 * m \<or> a = Suc (2 * m)" by (metis geod.elims)
    then have "m < 2^n" using a by auto
    consider "a = 2 * m" | "a = Suc(2*m)" using m by auto
    then show "dist (geod (Suc n) a) (geod (Suc n) (Suc a)) = dist x0 y0 / (2 * 2 ^ n)"
    proof (cases)
      case 1
      show ?thesis
        unfolding 1 apply auto
        unfolding middle using Suc.IH \<open>m < 2^n\<close> by auto
    next
      case 2
      have *: "Suc (Suc (2 * m)) = 2 * (Suc m)" by auto
      show ?thesis
        unfolding 2 apply auto
        unfolding * geod.simps(3) middle using Suc.IH \<open>m < 2^n\<close> by auto
    qed
  qed
qed

lemma geod_mult:
  "geod n a = geod (n + k) (a * 2^k)"
apply (induction k, auto) using geod.simps(3) by (metis mult.left_commute)

lemma geod_0:
  "geod n 0 = x0"
by (induction n, auto, metis geod.simps(3) semiring_normalization_rules(10))

lemma geod_end:
  "geod n (2^n) = y0"
by (induction n, auto)

text \<open>By the triangular inequality, the distance between points separated by $(b-a)/2^n$ is at
most $D * (b-a)/2^n$.\<close>

lemma geod_upper:
  assumes "a \<le> b" "b \<le> 2^n"
  shows "dist (geod n a) (geod n b) \<le> (b-a) * dist x0 y0 / 2^n"
proof -
  have *: "a+k > 2^n \<or> dist (geod n a) (geod n (a+k)) \<le> k * dist x0 y0 / 2^n" for k
  proof (induction k)
    case 0 then show ?case by auto
  next
    case (Suc k)
    show ?case
    proof (cases "2 ^ n < a + Suc k")
      case True then show ?thesis by auto
    next
      case False
      then have *: "a + k < 2 ^ n" by auto
      have "dist (geod n a) (geod n (a + Suc k)) \<le> dist (geod n a) (geod n (a+k)) + dist (geod n (a+k)) (geod n (a+Suc k))"
        using dist_triangle by auto
      also have "... \<le> k * dist x0 y0 / 2^n + dist x0 y0 / 2^n"
        using Suc.IH * geod_distance_successor by auto
      finally show ?thesis
        by (simp add: add_divide_distrib distrib_left mult.commute)
    qed
  qed
  show ?thesis using *[of "b-a"] assms by (simp add: of_nat_diff)
qed

text \<open>In fact, the distance is exactly $D * (b-a)/2^n$, otherwise the extremities of the interval
would be closer than $D$, a contradiction.\<close>

lemma geod_dist:
  assumes "a \<le> b" "b \<le> 2^n"
  shows "dist (geod n a) (geod n b) = (b-a) * dist x0 y0 / 2^n"
proof -
  have "dist (geod n a) (geod n b) \<le> (real b-a) * dist x0 y0 / 2^n"
    using geod_upper[of a b n] assms by auto
  moreover have "\<not> (dist (geod n a) (geod n b) < (real b-a) * dist x0 y0 / 2^n)"
  proof (rule ccontr, simp)
    assume *: "dist (geod n a) (geod n b) < (real b-a) * dist x0 y0 / 2^n"
    have "dist x0 y0 = dist (geod n 0) (geod n (2^n))"
      using geod_0 geod_end by auto
    also have "... \<le> dist (geod n 0) (geod n a) + dist (geod n a) (geod n b) + dist (geod n b) (geod n (2^n))"
      using dist_triangle4 by auto
    also have "... < a * dist x0 y0 / 2^n + (real b-a) * dist x0 y0 / 2^n + (2^n - real b) * dist x0 y0 / 2^n"
      using * assms geod_upper[of 0 a n] geod_upper[of b "2^n" n] by (auto intro: mono_intros)
    also have "... = dist x0 y0"
      using assms by (auto simp add: algebra_simps divide_simps)
    finally show "False" by auto
  qed
  ultimately show ?thesis by auto
qed

text \<open>We deduce the same statement but for points that are not on the same level, by putting
them on a common multiple level.\<close>

lemma geod_dist2:
  assumes "a \<le> 2^n" "b \<le> 2^p" "a/2^n \<le> b / 2^p"
  shows "dist (geod n a) (geod p b) = (b/2^p - a/2^n) * dist x0 y0"
proof -
  define r where "r = max n p"
  define ar where "ar = a * 2^(r - n)"
  have a: "ar / 2^r = a / 2^n"
    unfolding ar_def r_def by (auto simp add: divide_simps semiring_normalization_rules(26))
  have A: "geod r ar = geod n a"
    unfolding ar_def r_def using geod_mult[of n a "max n p - n"] by auto
  define br where "br = b * 2^(r - p)"
  have b: "br / 2^r = b / 2^p"
    unfolding br_def r_def by (auto simp add: divide_simps semiring_normalization_rules(26))
  have B: "geod r br = geod p b"
    unfolding br_def r_def using geod_mult[of p b "max n p - p"] by auto

  have "dist (geod n a) (geod p b) = dist (geod r ar) (geod r br)"
    using A B by auto
  also have "... = (real br - ar) * dist x0 y0 / 2 ^r"
    apply (rule geod_dist)
    using \<open>a/2^n \<le> b / 2^p\<close> unfolding a[symmetric] b[symmetric] apply (auto simp add: divide_simps)
    using \<open>b \<le> 2^p\<close> b apply (auto simp add: divide_simps)
    by (metis br_def le_add_diff_inverse2 max.cobounded2 mult.commute mult_le_mono2 r_def semiring_normalization_rules(26))
  also have "... = (real br / 2^r - real ar / 2^r) * dist x0 y0"
    by (auto simp add: algebra_simps divide_simps)
  finally show ?thesis using a b by auto
qed

text \<open>Same thing but without a priori ordering of the points.\<close>

lemma geod_dist3:
  assumes "a \<le> 2^n" "b \<le> 2^p"
  shows "dist (geod n a) (geod p b) = abs(b/2^p - a/2^n) * dist x0 y0"
apply (cases "a /2^n \<le> b/2^p", auto)
apply (rule geod_dist2[OF assms], auto)
apply (subst dist_commute, rule geod_dist2[OF assms(2) assms(1)], auto)
done

text \<open>Finally, we define a geodesic by extending what we have already defined on dyadic points,
thanks to the result of isometric extension of isometries taking their values
in complete spaces.\<close>

lemma geod:
  shows "\<exists>g. isometry_on {0..dist x0 y0} g \<and> g 0 = x0 \<and> g (dist x0 y0) = y0"
proof (cases "x0 = y0")
  case True
  show ?thesis apply (rule exI[of _ "\<lambda>_. x0"]) unfolding isometry_on_def using True by auto
next
  case False
  define A where "A = {(real k/2^n) * dist x0 y0 |k n. k \<le> 2^n}"
  have "{0..dist x0 y0} \<subseteq> closure A"
  proof (auto simp add: closure_approachable dist_real_def)
    fix t::real assume t: "0 \<le> t" "t \<le> dist x0 y0"
    fix e:: real assume "e > 0"
    then obtain n::nat where n: "dist x0 y0/e < 2^n"
      using one_less_numeral_iff real_arch_pow semiring_norm(76) by blast
    define k where "k = floor (2^n * t/ dist x0 y0)"
    have "k \<le> 2^n * t/ dist x0 y0" unfolding k_def by auto
    also have "... \<le> 2^n" using t False by (auto simp add: algebra_simps divide_simps)
    finally have "k \<le> 2^n" by auto
    have "k \<ge> 0" using t False unfolding k_def by auto
    define l where "l = nat k"
    have "k = int l" "l \<le> 2^n" using \<open>k \<ge> 0\<close> \<open>k \<le> 2^n\<close> nat_le_iff unfolding l_def by auto

    have "abs (2^n * t/dist x0 y0 - k) \<le> 1" unfolding k_def by linarith
    then have "abs(t - k/2^n * dist x0 y0) \<le> dist x0 y0 / 2^n"
      by (auto simp add: algebra_simps divide_simps False)
    also have "... < e" using n \<open>e > 0\<close> by (auto simp add: algebra_simps divide_simps)
    finally have "abs(t - k/2^n * dist x0 y0) < e" by auto
    then have "abs(t - l/2^n * dist x0 y0) < e" using \<open>k = int l\<close> by auto
    moreover have "l/2^n * dist x0 y0 \<in> A" unfolding A_def using \<open>l \<le> 2^n\<close> by auto
    ultimately show "\<exists>u\<in>A. abs(u - t) < e" by force
  qed

  text \<open>For each dyadic point, we choose one representation of the form $K/2^N$, it is not important
  for us that it is the minimal one.\<close>
  define index where "index = (\<lambda>t. SOME i. t = real (fst i)/2^(snd i) * dist x0 y0 \<and> (fst i) \<le> 2^(snd i))"
  define K where "K = (\<lambda>t. fst (index t))"
  define N where "N = (\<lambda>t. snd (index t))"
  have t: "t = K t/ 2^(N t) * dist x0 y0 \<and> K t \<le> 2^(N t)" if "t \<in> A" for t
  proof -
    obtain n k::nat where "t = k/2^n * dist x0 y0" "k \<le> 2^n" using \<open>t\<in> A\<close> unfolding A_def by auto
    then have *: "\<exists>i. t = real (fst i)/2^(snd i) * dist x0 y0 \<and> (fst i) \<le> 2^(snd i)" by auto
    show ?thesis unfolding K_def N_def index_def using someI_ex[OF *] by auto
  qed

  text \<open>We can now define our function on dyadic points.\<close>
  define f where "f = (\<lambda>t. geod (N t) (K t))"
  have "0 \<in> A" unfolding A_def by auto
  have "f 0 = x0"
  proof -
    have "0 = K 0 /2^(N 0) * dist x0 y0" using t \<open>0 \<in> A\<close> by auto
    then have "K 0 = 0" using False by auto
    then show ?thesis unfolding f_def using geod_0 by auto
  qed
  have "dist x0 y0 = (real 1/2^0) * dist x0 y0" by auto
  then have "dist x0 y0 \<in> A" unfolding A_def by force
  have "f (dist x0 y0) = y0"
  proof -
    have "dist x0 y0 = K (dist x0 y0) / 2^(N (dist x0 y0)) * dist x0 y0"
      using t \<open>dist x0 y0 \<in> A\<close> by auto
    then have "K (dist x0 y0) = 2^(N(dist x0 y0))" using False by (auto simp add: divide_simps)
    then show ?thesis unfolding f_def using geod_end by auto
  qed
  text \<open>By construction, it is an isometry on dyadic points.\<close>
  have "isometry_on A f"
  proof (rule isometry_onI)
    fix s t assume inA: "s \<in> A" "t \<in> A"
    have "dist (f s) (f t) = abs (K t/2^(N t) - K s/2^(N s)) * dist x0 y0"
      unfolding f_def apply (rule geod_dist3) using t inA by auto
    also have "... = abs(K t/2^(N t) * dist x0 y0 - K s/2^(N s) * dist x0 y0)"
      by (auto simp add: abs_mult_pos left_diff_distrib)
    also have "... = abs(t - s)"
      using t inA by auto
    finally show "dist (f s) (f t) = dist s t" unfolding dist_real_def by auto
  qed
  text \<open>We can thus extend it to an isometry on the closure of dyadic points.
  It is the desired geodesic.\<close>
  then obtain g where g: "isometry_on (closure A) g" "\<And>t. t \<in> A \<Longrightarrow> g t = f t"
    using isometry_extend_closure by metis
  have "isometry_on {0..dist x0 y0} g"
    by (rule isometry_on_subset[OF \<open>isometry_on (closure A) g\<close> \<open>{0..dist x0 y0} \<subseteq> closure A\<close>])
  moreover have "g 0 = x0"
    using g(2)[OF \<open>0 \<in> A\<close>] \<open>f 0 = x0\<close> by simp
  moreover have "g (dist x0 y0) = y0"
    using g(2)[OF \<open>dist x0 y0 \<in> A\<close>] \<open>f (dist x0 y0) = y0\<close> by simp
  ultimately show ?thesis by auto
qed

end

text \<open>We can now complete the proof that a complete space with middles is in fact geodesic:
all the work has been done in the locale \verb+complete_space_with_middle+, in Lemma~\verb+geod+.\<close>

theorem complete_with_middles_imp_geodesic:
  assumes "\<And>x y::('a::complete_space). \<exists>m. dist x m = dist x y /2 \<and> dist m y = dist x y /2"
  shows "OFCLASS('a, geodesic_space_class)"
proof (standard, rule geodesic_subsetI)
  fix x0 y0::'a
  interpret complete_space_with_middle x0 y0
    apply standard using assms by auto
  have "\<exists>g. g 0 = x0 \<and> g (dist x0 y0) = y0 \<and> isometry_on {0..dist x0 y0} g"
    using geod by auto
  then show "\<exists>G. geodesicSegmentBetween G x0 y0 \<and> G \<subseteq> UNIV"
    unfolding geodesicSegmentBetween_def by auto
qed
