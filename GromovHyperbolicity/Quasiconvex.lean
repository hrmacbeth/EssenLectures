/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD -/
import GromovHyperbolicity.GromovHyperbolic
import Mathlib.Tactic.Peel

-- imports "HOL-Decision_Procs.Approximation"
-- hide_const (open) Approximation.Min
-- hide_const (open) Approximation.Max

/-! # Quasiconvexity -/

open Metric

variable {M : Type*} [MetricSpace M]

/-- In a Gromov-hyperbolic setting, convexity is not a well-defined notion as everything should
be coarse. The good replacement is quasi-convexity: A set $X$ is $C$-quasi-convex if any pair of
points in $X$ can be joined by a geodesic that remains within distance $C$ of $X$. One could also
require this for all geodesics, up to changing $C$, as two geodesics between the same endpoints
remain within uniformly bounded distance. We use the first definition to ensure that a geodesic is
$0$-quasi-convex. -/
def quasiconvex (C : ℝ) (X : Set M) : Prop :=
  C ≥ 0 ∧ (∀ x ∈ X, ∀ y ∈ X, ∃ G, geodesic_segment_between G x y ∧ (∀ z ∈ G, infDist z X ≤ C))

variable {C D : ℝ} {X G : Set M}

lemma quasiconvexD (h : quasiconvex C X) {x y : M} (hx : x ∈ X) (hy : y∈X) :
    ∃ G, geodesic_segment_between G x y ∧ (∀ z ∈ G, infDist z X ≤ C) := by
  aesop (add norm unfold quasiconvex)
-- using assms unfolding quasiconvex_def by auto

lemma quasiconvexC (h : quasiconvex C X) : C ≥ 0 := by
  aesop (add norm unfold quasiconvex)
-- using assms unfolding quasiconvex_def by auto

lemma quasiconvexI (hC : C ≥ 0)
    (hCX : ∀ x y, x ∈ X → y ∈ X → (∃ G, geodesic_segment_between G x y ∧ (∀ z ∈ G, infDist z X ≤ C))) :
    quasiconvex C X := by
  aesop (add norm unfold quasiconvex)
-- using assms unfolding quasiconvex_def by auto

lemma quasiconvex_of_geodesic {G : Set M} (hG : geodesic_segment G) : quasiconvex 0 G := by
  sorry
-- proof (rule quasiconvexI, simp)
--   fix x y assume *: "x∈G" "y∈G"
--   obtain H where H: "H \<subseteq> G" "geodesic_segment_between H x y"
--     using geodesic_subsegment_exists[OF assms(1) *] by auto
--   have "infDist z G ≤ 0" if "z∈H" for z
--     using H(1) that by auto
--   then show "∃ H. geodesic_segment_between H x y ∧ (∀ z ∈ H. infDist z G ≤ 0)"
--     using H(2) by auto
-- qed

lemma quasiconvex_empty (hC : C ≥ 0) : quasiconvex C (∅ : Set M) := by
  aesop (add norm unfold quasiconvex)
-- unfolding quasiconvex_def using assms by auto

lemma quasiconvex_mono (hCD : C ≤ D) (hC : quasiconvex C G) : quasiconvex D G := by
  obtain ⟨h1, h2⟩ := hC
  refine ⟨by linarith, ?_⟩
  peel h2
  linarith
-- using assms unfolding quasiconvex_def by (auto, fastforce)

variable [Gromov_hyperbolic_space M] [GeodesicSpace M]

set_option quotPrecheck false in
notation "δ" => Gromov_hyperbolic_space.deltaG M

/-- The $r$-neighborhood of a quasi-convex set is still quasi-convex in a hyperbolic space,
for a constant that does not depend on $r$. -/
lemma quasiconvex_thickening [Inhabited M] (h : quasiconvex C X) (hr : r ≥ 0) :
    quasiconvex (C + 8 * δ) (⋃ x ∈ X, closedBall x r) := by
  classical
  apply quasiconvexI
  · have := quasiconvexC h
    have := delta_nonneg M
    positivity
  intro y z hy hz
  refine ⟨{y‒z}, sorry, ?_⟩
  sorry
-- proof (rule quasiconvexI)
--   show "C + 8 * δ ≥ 0" using quasiconvexC[OF assms(1)] by simp
-- next
--   fix y z assume *: "y∈(\<Union>x ∈ X. cball x r)" "z∈(\<Union>x ∈ X. cball x r)"
--   have A: "infDist w (\<Union>x ∈ X. cball x r) ≤ C + 8 * deltaG TYPE('a)" if "w∈{y--z}" for w
--   proof -
--     obtain py where py: "py∈X" "y∈cball py r"
--       using * by auto
--     obtain pz where pz: "pz∈X" "z∈cball pz r"
--       using * by auto
--     obtain G where G: "geodesic_segment_between G py pz" "(∀ p ∈ G. infDist p X ≤ C)"
--       using quasiconvexD[OF assms(1) \<open>py∈X\<close> \<open>pz∈X\<close>] by auto
--     have A: "infDist w ({y--py} \<union> G \<union> {pz--z}) ≤ 8 * δ"
--       by (rule thin_quadrilaterals[OF _ G(1) _ _ \<open>w∈{y--z}\<close>, where ?x = y and ?t = z], auto)
--     have "∃ u∈{y--py} \<union> G \<union> {pz--z}. infDist w ({y--py} \<union> G \<union> {pz--z}) = dist w u"
--       apply (rule infDist_proper_attained, auto intro!: proper_Un simp add: geodesic_segment_topology(7))
--       by (meson G(1) geodesic_segmentI geodesic_segment_topology(7))
--     then obtain u where u: "u∈{y--py} \<union> G \<union> {pz--z}" "infDist w ({y--py} \<union> G \<union> {pz--z}) = dist w u"
--       by auto
--     then consider "u∈{y--py}" | "u∈G" | "u∈{pz--z}" by auto
--     then have "infDist u (\<Union>x ∈ X. cball x r) ≤ C"
--     proof (cases)
--       case 1
--       then have "dist py u ≤ dist py y"
--         using geodesic_segment_dist_le local.some_geodesic_is_geodesic_segment(1) some_geodesic_commute some_geodesic_endpoints(1) by blast
--       also have "... ≤ r"
--         using py(2) by auto
--       finally have "u∈cball py r"
--         by auto
--       then have "u∈(\<Union>x ∈ X. cball x r)"
--         using py(1) by auto
--       then have "infDist u (\<Union>x ∈ X. cball x r) = 0"
--         by auto
--       then show ?thesis
--         using quasiconvexC[OF assms(1)] by auto
--     next
--       case 3
--       then have "dist pz u ≤ dist pz z"
--         using geodesic_segment_dist_le local.some_geodesic_is_geodesic_segment(1) some_geodesic_commute some_geodesic_endpoints(1) by blast
--       also have "... ≤ r"
--         using pz(2) by auto
--       finally have "u∈cball pz r"
--         by auto
--       then have "u∈(\<Union>x ∈ X. cball x r)"
--         using pz(1) by auto
--       then have "infDist u (\<Union>x ∈ X. cball x r) = 0"
--         by auto
--       then show ?thesis
--         using quasiconvexC[OF assms(1)] by auto
--     next
--       case 2
--       have "infDist u (\<Union>x ∈ X. cball x r) ≤ infDist u X"
--         apply (rule infDist_mono) using assms(2) py(1) by auto
--       then show ?thesis using 2 G(2) by auto
--     qed
--     moreover have "infDist w (\<Union>x ∈ X. cball x r) ≤ infDist u (\<Union>x ∈ X. cball x r) + dist w u"
--       by (intro mono_intros)
--     ultimately show ?thesis
--       using A u(2) by auto
--   qed
--   show "∃ G. geodesic_segment_between G y z ∧ (∀ w ∈ G. infDist w (\<Union>x ∈ X. cball x r) ≤ C + 8 * deltaG TYPE('a))"
--     apply (rule exI[of _ "{y--z}"]) using A by auto
-- qed

/-- If $x$ has a projection $p$ on a quasi-convex set $G$, then all segments from a point in $G$
to $x$ go close to $p$, i.e., the triangular inequality $d(x,y) \leq d(x,p) + d(p,y)$ is essentially
an equality, up to an additive constant. -/
lemma dist_along_quasiconvex (hCG : quasiconvex C G) (hp : p ∈ proj_set x G) (hy : y ∈ G) :
    dist x p + dist p y ≤ dist x y + 4 * δ + 2 * C := by
  sorry
-- proof -
--   have *: "p∈G"
--     using assms proj_setD by auto
--   obtain H where H: "geodesic_segment_between H p y" "∧q. q∈H \<Longrightarrow> infDist q G ≤ C"
--     using quasiconvexD[OF assms(1) * assms(3)] by auto
--   have "∃ m ∈ H. infDist x H = dist x m"
--     apply (rule infDist_proper_attained[of H x]) using geodesic_segment_topology[OF geodesic_segmentI[OF H(1)]] by auto
--   then obtain m where m: "m∈H" "infDist x H = dist x m" by auto
--   then have I: "dist x m ≤ Gromov_product_at x p y + 2 * δ"
--     using infDist_triangle_side[OF H(1), of x] by auto
--   have "dist x p - dist x m - C ≤ e" if "e > 0" for e
--   proof -
--     have "∃ r ∈ G. dist m r < infDist m G + e"
--       apply (rule infDist_almost_attained) using \<open>e > 0\<close> assms(3) by auto
--     then obtain r where r: "r∈G" "dist m r < infDist m G + e"
--       by auto
--     then have *: "dist m r ≤ C + e" using H(2)[OF \<open>m∈H\<close>] by auto
--     have "dist x p ≤ dist x r"
--       using \<open>r∈G\<close> assms(2) proj_set_dist_le by blast
--     also have "... ≤ dist x m + dist m r"
--       by (intro mono_intros)
--     finally show ?thesis using * by (auto simp add: metric_space_class.dist_commute)
--   qed
--   then have "dist x p - dist x m - C ≤ 0"
--     using dense_ge by blast
--   then show ?thesis
--     using I unfolding Gromov_product_at_def by (auto simp add: algebra_simps divide_simps)
-- qed

/-- The next lemma is~\<^cite> Proposition 10.2.1 in "coornaert_delzant_papadopoulos" with better
constants. It states that the distance between the projections
on a quasi-convex set is controlled by the distance of the original points, with a gain given by the
distances of the points to the set. -/
lemma proj_along_quasiconvex_contraction (h : quasiconvex C G) (hx : px ∈ proj_set x G)
    (hy : py ∈ proj_set y G) :
    dist px py ≤ max (5 * δ + 2 * C) (dist x y - dist px x - dist py y + 10 * δ + 4 * C) := by
  sorry
-- proof -
--   have "px∈G" "py∈G"
--     using assms proj_setD by auto
--   have "(dist x px + dist px py - 4 * δ - 2 * C) + (dist y py + dist py px - 4 *δ - 2 * C)
--         ≤ dist x py + dist y px"
--     apply (intro mono_intros)
--     using dist_along_quasiconvex[OF assms(1) assms(2) \<open>py∈G\<close>] dist_along_quasiconvex[OF assms(1) assms(3) \<open>px∈G\<close>] by auto
--   also have "... ≤ max (dist x y + dist py px) (dist x px + dist py y) + 2 * δ"
--     by (rule hyperb_quad_ineq)
--   finally have *: "dist x px + dist y py + 2 * dist px py
--           ≤ max (dist x y + dist py px) (dist x px + dist py y) + 10 * δ + 4 * C"
--     by (auto simp add: metric_space_class.dist_commute)
--   show ?thesis
--   proof (cases "dist x y + dist py px ≥ dist x px + dist py y")
--     case True
--     then have "dist x px + dist y py + 2 * dist px py ≤ dist x y + dist py px + 10 * δ + 4 * C"
--       using * by auto
--     then show ?thesis by (auto simp add: metric_space_class.dist_commute)
--   next
--     case False
--     then have "dist x px + dist y py + 2 * dist px py ≤ dist x px + dist py y + 10 * δ + 4 * C"
--       using * by auto
--     then show ?thesis by (simp add: metric_space_class.dist_commute)
--   qed
-- qed

/-- The projection on a quasi-convex set is $1$-Lipschitz up to an additive error. -/
lemma proj_along_quasiconvex_contraction' (h : quasiconvex C G) (hx : px ∈ proj_set x G)
    (hy : py ∈ proj_set y G) :
    dist px py ≤ dist x y + 4 * δ + 2 * C := by
  by_cases hxy : dist y py ≤ dist x px
  · have :=
    calc dist x px + dist px py ≤ dist x py + 4 * δ + 2 * C :=
          dist_along_quasiconvex h hx <| proj_setD hy
      _ ≤ (dist x y + dist y py) + 4 * δ + 2 * C := by
          gcongr
          exact dist_triangle x y py
      _ ≤ (dist x y + dist x px) + 4 * δ + 2 * C := by gcongr
    linarith
  · push_neg at hxy
    have :=
    calc dist y py + dist py px ≤ dist y px + 4 * δ + 2 * C :=
          dist_along_quasiconvex h hy <| proj_setD hx
      _ ≤ (dist y x + dist x px) + 4 * δ + 2 * C := by
          gcongr
          exact dist_triangle y x px
      _ < (dist y x + dist y py) + 4 * δ + 2 * C := by gcongr
    simp only [dist_comm] at this ⊢
    linarith
-- proof (cases "dist y py ≤ dist x px")
--   case True
--   have "dist x px + dist px py ≤ dist x py + 4 * δ + 2 * C"
--     by (rule dist_along_quasiconvex[OF assms(1) assms(2) proj_setD(1)[OF assms(3)]])
--   also have "... ≤ (dist x y + dist y py) + 4 * δ + 2 * C"
--     by (intro mono_intros)
--   finally show ?thesis using True by auto
-- next
--   case False
--   have "dist y py + dist py px ≤ dist y px + 4 * δ + 2 * C"
--     by (rule dist_along_quasiconvex[OF assms(1) assms(3) proj_setD(1)[OF assms(2)]])
--   also have "... ≤ (dist y x + dist x px) + 4 * δ + 2 * C"
--     by (intro mono_intros)
--   finally show ?thesis using False by (auto simp add: metric_space_class.dist_commute)
-- qed

/-- We can in particular specialize the previous statements to geodesics, which are
$0$-quasi-convex. -/
lemma dist_along_geodesic (h : geodesic_segment G) (hx : p ∈ proj_set x G) (hy : y ∈ G) :
    dist x p + dist p y ≤ dist x y + 4 * δ := by
  have H := dist_along_quasiconvex (quasiconvex_of_geodesic h) hx hy
  ring_nf at H ⊢
  exact H
-- using dist_along_quasiconvex[OF quasiconvex_of_geodesic[OF assms(1)] assms(2) assms(3)] by auto

lemma proj_along_geodesic_contraction (h : geodesic_segment G) (hx : px ∈ proj_set x G)
    (hy : py ∈ proj_set y G) :
    dist px py ≤ max (5 * δ) (dist x y - dist px x - dist py y + 10 * δ) := by
  have H := proj_along_quasiconvex_contraction (quasiconvex_of_geodesic h) hx hy
  ring_nf at H ⊢
  exact H
-- using proj_along_quasiconvex_contraction[OF quasiconvex_of_geodesic[OF assms(1)] assms(2) assms(3)] by auto

lemma proj_along_geodesic_contraction' (h : geodesic_segment G) (hx : px ∈ proj_set x G)
    (hy : py ∈ proj_set y G) :
    dist px py ≤ dist x y + 4 * δ := by
  have H := proj_along_quasiconvex_contraction' (quasiconvex_of_geodesic h) hx hy
  ring_nf at H ⊢
  exact H
-- using proj_along_quasiconvex_contraction'[OF quasiconvex_of_geodesic[OF assms(1)] assms(2) assms(3)] by auto

/-- If one projects a continuous curve on a quasi-convex set, the image does not have to be
connected (the projection is discontinuous), but since the projections of nearby points are within
uniformly bounded distance one can find in the projection a point with almost prescribed distance
to the starting point, say. For further applications, we also pick the first such point, i.e.,
all the previous points are also close to the starting point. -/
-- not sure whether inequalities are sharp or non-sharp
lemma quasi_convex_projection_small_gaps {f p : ℝ → M} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hab : a ≤ b)
    (h : quasiconvex C G)
    (hfG : ∀ t ∈ Set.Icc a b, p t ∈ proj_set (f t) G)
    (hdelta : delta > δ)
    (hd : d ∈ Set.Icc (4 * delta + 2 * C) (dist (p a) (p b))) :
    ∃ t ∈ Set.Icc a b, (dist (p a) (p t) ∈ Set.Icc (d - 4 * delta - 2 * C) d)
                    ∧ (∀ s ∈ Set.Icc a t, dist (p a) (p s) ≤ d) := by
  sorry
-- proof -
--   have "delta > 0"
--     using assms(5) local.delta_nonneg by linarith
--   moreover have "C ≥ 0"
--     using quasiconvexC[OF assms(3)] by simp
--   ultimately have "d ≥ 0" using assms by auto

--   /- The idea is to define the desired point as the last point $u$ for which there is a projection
--   at distance at most $d$ of the starting point. Then the projection can not be much closer to
--   the starting point, or one could point another such point further away by almost continuity, giving
--   a contradiction. The technical implementation requires some care, as the "last point" may not
--   satisfy the property, for lack of continuity. If it does, then fine. Otherwise, one should go just
--   a little bit to its left to find the desired point. -/
--   define I where "I = {t∈{a..b}. ∀ s∈{a..t}. dist (p a) (p s) ≤ d}"
--   have "a∈I"
--     using \<open>a ≤ b\<close> \<open>d ≥ 0\<close> unfolding I_def by auto
--   have "bdd_above I"
--     unfolding I_def by auto
--   define u where "u = Sup I"
--   have "a ≤ u"
--     unfolding u_def apply (rule cSup_upper) using \<open>a∈I\<close> \<open>bdd_above I\<close> by auto
--   have "u ≤ b"
--     unfolding u_def apply (rule cSup_least) using \<open>a∈I\<close> apply auto unfolding I_def by auto
--   have A: "dist (p a) (p s) ≤ d" if "s < u" "a ≤ s" for s
--   proof -
--     have "∃ t ∈ I. s < t"
--       unfolding u_def apply (subst less_cSup_iff[symmetric])
--       using \<open>a∈I\<close> \<open>bdd_above I\<close> using \<open>s < u\<close> unfolding u_def by auto
--     then obtain t where t: "t∈I" "s < t" by auto
--     then have "s∈{a..t}" using \<open>a ≤ s\<close> by auto
--     then show ?thesis
--       using t(1) unfolding I_def by auto
--   qed
--   have "continuous (at u within {a..b}) f"
--     using assms(1) by (simp add: \<open>a ≤ u\<close> \<open>u ≤ b\<close> continuous_on_eq_continuous_within)
--   then have "∃ i > 0. ∀ s ∈ {a..b}. dist u s < i \<longrightarrow> dist (f u) (f s) < (delta - δ)"
--     unfolding continuous_within_eps_delta using \<open>δ < delta\<close> by (auto simp add: metric_space_class.dist_commute)
--   then obtain e0 where e0: "e0 > 0" "∧s. s∈{a..b} \<Longrightarrow> dist u s < e0 \<Longrightarrow> dist (f u) (f s) < (delta - δ)"
--     by auto

--   show ?thesis
--   proof (cases "dist (p a) (p u) > d")
--     /- First, consider the case where $u$ does not satisfy the defining property. Then the
--     desired point $t$ is taken slightly to its left. -/
--     case True
--     then have "u \<noteq> a"
--       using \<open>d ≥ 0\<close> by auto
--     then have "a < u" using \<open>a ≤ u\<close> by auto

--     define e::real where "e = min (e0/2) ((u-a)/2)"
--     then have "e > 0" using \<open>a < u\<close> \<open>e0 > 0\<close> by auto
--     define t where "t = u - e"
--     then have "t < u" using \<open>e > 0\<close> by auto
--     have "u - b ≤ e" "e ≤ u - a"
--       using \<open>e > 0\<close> \<open>u ≤ b\<close> unfolding e_def by (auto simp add: min_def)
--     then have "t∈{a..b}" "t∈{a..t}"
--       unfolding t_def by auto
--     have "dist u t < e0"
--       unfolding t_def e_def dist_real_def using \<open>e0 > 0\<close> \<open>a ≤ u\<close> by auto
--     have *: "∀ s∈{a..t}. dist (p a) (p s) ≤ d"
--       using A \<open>t < u\<close> by auto
--     have "dist (p t) (p u) ≤ dist (f t) (f u) + 4 * δ + 2 * C"
--       apply (rule proj_along_quasiconvex_contraction'[OF \<open>quasiconvex C G\<close>])
--       using assms (4) \<open>t∈{a..b}\<close> \<open>a ≤ u\<close> \<open>u ≤ b\<close> by auto
--     also have "... ≤ (delta - δ) + 4 * δ + 2 * C"
--       apply (intro mono_intros)
--       using e0(2)[OF \<open>t∈{a..b}\<close> \<open>dist u t < e0\<close>] by (auto simp add: metric_space_class.dist_commute)
--     finally have I: "dist (p t) (p u) ≤ 4 * delta + 2 * C"
--       using \<open>delta > δ\<close> by simp

--     have "d ≤ dist (p a) (p u)"
--       using True by auto
--     also have "... ≤ dist (p a) (p t) + dist (p t) (p u)"
--       by (intro mono_intros)
--     also have "... ≤ dist (p a) (p t) + 4 * delta + 2 * C"
--       using I by simp
--     finally have **: "d - 4 * delta - 2 * C ≤ dist (p a) (p t)"
--       by simp
--     show ?thesis
--       apply (rule bexI[OF _ \<open>t∈{a..b}\<close>]) using * ** \<open>t∈{a..b}\<close> by auto
--   next
--     /- Next, consider the case where $u$ satisfies the defining property. Then we will take $t = u$.
--     The only nontrivial point to check is that the distance of $f(u)$ to the starting point is not
--     too small. For this, we need to separate the case where $u = b$ (in which case one argues directly)
--     and the case where $u < b$, where one can use a point slightly to the right of $u$ which has a
--     projection at distance $ > d$ of the starting point, and use almost continuity. -/
--     case False
--     have B: "dist (p a) (p s) ≤ d" if "s∈{a..u}" for s
--     proof (cases "s = u")
--       case True
--       show ?thesis
--         unfolding True using False by auto
--     next
--       case False
--       then show ?thesis
--         using that A by auto
--     qed
--     have C: "dist (p a) (p u) ≥ d - 4 *delta - 2 * C"
--     proof (cases "u = b")
--       case True
--       have "d ≤ dist (p a) (p b)"
--         using assms by auto
--       also have "... ≤ dist (p a) (p u) + dist (p u) (p b)"
--         by (intro mono_intros)
--       also have "... ≤ dist (p a) (p u) + (dist (f u) (f b) + 4 * deltaG TYPE('a) + 2 * C)"
--         apply (intro mono_intros proj_along_quasiconvex_contraction'[OF \<open>quasiconvex C G\<close>])
--         using assms \<open>a ≤ u\<close> \<open>u ≤ b\<close> by auto
--       finally show ?thesis
--         unfolding True using \<open>δ < delta\<close> by auto
--     next
--       case False
--       then have "u < b"
--         using \<open>u ≤ b\<close> by auto
--       define e::real where "e = min (e0/2) ((b-u)/2)"
--       then have "e > 0" using \<open>u < b\<close> \<open>e0 > 0\<close> by auto
--       define v where "v = u + e"
--       then have "u < v"
--         using \<open>e > 0\<close> by auto
--       have "e ≤ b - u" "a - u ≤ e"
--         using \<open>e > 0\<close> \<open>a ≤ u\<close> unfolding e_def by (auto simp add: min_def)
--       then have "v∈{a..b}"
--         unfolding v_def by auto
--       moreover have "v \<notin> I"
--         using \<open>u < v\<close> \<open>bdd_above I\<close> cSup_upper not_le unfolding u_def by auto
--       ultimately have "∃ w∈{a..v}. dist (p a) (p w) > d"
--         unfolding I_def by force
--       then obtain w where w: "w∈{a..v}" "dist (p a) (p w) > d"
--         by auto
--       then have "w \<notin> {a..u}"
--         using B by force
--       then have "u < w"
--         using w(1) by auto
--       have "w∈{a..b}"
--         using w(1) \<open>v∈{a..b}\<close> by auto
--       have "dist u w = w - u"
--         unfolding dist_real_def using \<open>u < w\<close> by auto
--       also have "... ≤ v - u"
--         using w(1) by auto
--       also have "... < e0"
--         unfolding v_def e_def min_def using \<open>e0 > 0\<close> by auto
--       finally have "dist u w < e0" by simp
--       have "dist (p u) (p w) ≤ dist (f u) (f w) + 4 * δ + 2 * C"
--         apply (rule proj_along_quasiconvex_contraction'[OF \<open>quasiconvex C G\<close>])
--         using assms \<open>a ≤ u\<close> \<open>u ≤ b\<close> \<open>w∈{a..b}\<close> by auto
--       also have "... ≤ (delta - δ) + 4 * δ + 2 * C"
--         apply (intro mono_intros)
--         using e0(2)[OF \<open>w∈{a..b}\<close> \<open>dist u w < e0\<close>] by (auto simp add: metric_space_class.dist_commute)
--       finally have I: "dist (p u) (p w) ≤ 4 * delta + 2 * C"
--         using \<open>delta > δ\<close> by simp
--       have "d ≤ dist (p a) (p u) + dist (p u) (p w)"
--         using w(2) metric_space_class.dist_triangle[of "p a" "p w" "p u"] by auto
--       also have "... ≤ dist (p a) (p u) + 4 * delta + 2 * C"
--         using I by auto
--       finally show ?thesis by simp
--     qed
--     show ?thesis
--       apply (rule bexI[of _ u])
--       using B \<open>a ≤ u\<close> \<open>u ≤ b\<close> C by auto
--   qed
-- qed

/-- Same lemma, except that one exchanges the roles of the beginning and the end point. -/
-- not sure whether inequalities are sharp or non-sharp
lemma quasi_convex_projection_small_gaps' {f p : ℝ → M} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hab : a ≤ b)
    (h : quasiconvex C G)
    (hfG : ∀ t ∈ Set.Icc a b, p t ∈ proj_set (f t) G)
    (hdelta : delta > δ)
    (hd : d ∈ Set.Icc (4 * delta + 2 * C) (dist (p a) (p b))) :
    ∃ t ∈ Set.Icc a b, (dist (p a) (p t) ∈ Set.Icc (d - 4 * delta - 2 * C) d)
                    ∧ (∀ s ∈ Set.Icc t b, dist (p b) (p s) ≤ d) := by
  sorry
--   have *: "continuous_on {-b..-a} (\<lambda>t. f(-t))"
--     using continuous_on_compose[of "{-b..-a}" "\<lambda>t. -t" f] using assms(1) continuous_on_minus[OF continuous_on_id] by auto
--   define q where "q = (\<lambda>t. p(-t))"
--   have "∃ t∈{-b..-a}. (dist (q (-b)) (q t)∈{d - 4 * delta - 2 * C .. d})
--                     ∧ (∀ s∈{-b..t}. dist (q (-b)) (q s) ≤ d)"
--     apply (rule quasi_convex_projection_small_gaps[where ?f = "\<lambda>t. f(-t)" and ?G = G])
--     unfolding q_def using assms * by (auto simp add: metric_space_class.dist_commute)
--   then obtain t where t: "t∈{-b..-a}" "dist (q (-b)) (q t)∈{d - 4 * delta - 2 * C .. d}"
--                       "∧s. s∈{-b..t} \<Longrightarrow> dist (q (-b)) (q s) ≤ d"
--     by blast
--   have *: "dist (p b) (p s) ≤ d" if "s∈{-t..b}" for s
--     using t(3)[of "-s"] that q_def by auto
--   show ?thesis
--     apply (rule bexI[of _ "-t"]) using t * q_def by auto
-- qed
