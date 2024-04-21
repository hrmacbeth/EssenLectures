/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD -/
import GromovHyperbolicity.GromovHyperbolic.Basic

/-!
# Gromov hyperbolic spaces
-/

open Metric

variable {X : Type*} [MetricSpace X]

variable {δ : ℝ} {A : Set X} in
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

variable {δ : ℝ} {A : Set X} in
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


variable [Gromov_hyperbolic_space X]

-- set_option quotPrecheck false in
local notation "δ" => Gromov_hyperbolic_space.deltaG X

open Gromov_hyperbolic_space


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
