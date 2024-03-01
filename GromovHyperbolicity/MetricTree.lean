/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD -/
import GromovHyperbolicity.GromovHyperbolic

/-!
# Metric trees
-/


/-- Metric trees have several equivalent definitions. The simplest one is probably that it
is a geodesic space in which the union of two geodesic segments intersecting only at one endpoint is
still a geodesic segment.

Metric trees are Gromov hyperbolic, with $\delta = 0$. -/
class metric_tree (X : Type*) [MetricSpace X] [GeodesicSpace X] : Prop where
  geod_union : ∀ x y z : X, geodesic_segment_between G x y → geodesic_segment_between H y z →
    G ∩ H = {y} → geodesic_segment_between (G ∪ H) x z

/-- We will now show that the real line is a metric tree, by identifying its geodesic
segments, i.e., the compact intervals. -/
lemma geodesic_segment_between_real {x y : ℝ} (hxy : x ≤ y) :
    geodesic_segment_between G x y ↔ (G = Set.Icc x y) := by
  sorry
-- proof
--   assume H: "geodesic_segment_between G x y"
--   then have "connected G" "x ∈ G" "y ∈ G"
--     using geodesic_segment_topology(2) geodesic_segmentI geodesic_segment_endpoints by auto
--   then have *: "{x..y} \<subseteq> G"
--     by (simp add: connected_contains_Icc)
--   moreover have "G \<subseteq> {x..y}"
--   proof
--     fix s assume "s ∈ G"
--     have "abs(s-x) + abs(s-y) = abs(x-y)"
--       using geodesic_segment_dist[OF H \<open>s ∈ G -/] unfolding dist_real_def by auto
--     then show "s ∈ {x..y}" using \<open>x ≤ y -/ by auto
--   qed
--   ultimately show "G = {x..y}" by auto
-- next
--   assume H: "G = {x..y}"
--   define g where "g = (\<lambda>t. t + x)"
--   have "g 0 = x \<and> g (dist x y) = y \<and> isometry_on {0..dist x y} g \<and> G = g ` {0..dist x y}"
--     unfolding g_def isometry_on_def H using \<open>x ≤ y -/ by (auto simp add: dist_real_def)
--   then have "\<exists>g. g 0 = x \<and> g (dist x y) = y \<and> isometry_on {0..dist x y} g \<and> G = g ` {0..dist x y}"
--     by auto
--   then show "geodesic_segment_between G x y" unfolding geodesic_segment_between_def by auto
-- qed

#exit

lemma geodesic_segment_between_real':
  "{x--y} = {min x y..max x (y::real)}"
by (metis geodesic_segment_between_real geodesic_segment_commute some_geodesic_is_geodesic_segment(1) max_def min.cobounded1 min_def)

lemma geodesic_segment_real:
  "geodesic_segment (G::real set) = (\<exists>x y. x ≤ y \<and> G = {x..y})"
proof
  assume "geodesic_segment G"
  then obtain x y where *: "geodesic_segment_between G x y" unfolding geodesic_segment_def by auto
  have "(x ≤ y \<and> G = {x..y}) \<or> (y ≤ x \<and> G = {y..x})"
    apply (rule le_cases[of x y])
    using geodesic_segment_between_real * geodesic_segment_commute apply simp
    using geodesic_segment_between_real * geodesic_segment_commute by metis
  then show "\<exists>x y. x ≤ y \<and> G = {x..y}" by auto
next
  assume "\<exists>x y. x ≤ y \<and> G = {x..y}"
  then show "geodesic_segment G"
    unfolding geodesic_segment_def using geodesic_segment_between_real by metis
qed

instance real::metric_tree
proof
  fix G H::"real set" and x y z::real assume GH: "geodesic_segment_between G x y" "geodesic_segment_between H y z" "G \<inter> H = {y}"
  have G: "G = {min x y..max x y}" using GH
    by (metis geodesic_segment_between_real geodesic_segment_commute inf_real_def inf_sup_ord(2) max.coboundedI2 max_def min_def)
  have H: "H = {min y z..max y z}" using GH
    by (metis geodesic_segment_between_real geodesic_segment_commute inf_real_def inf_sup_ord(2) max.coboundedI2 max_def min_def)
  have *: "(x ≤ y \<and> y ≤ z) \<or> (z ≤ y \<and> y ≤ x)"
    using G H \<open>G \<inter> H = {y} -/ unfolding min_def max_def
    apply auto
    apply (metis (mono_tags, opaque_lifting) min_le_iff_disj order_refl)
    by (metis (full_types) less_eq_real_def max_def)
  show "geodesic_segment_between (G ∪ H) x z"
    using * apply rule
    using \<open>G \<inter> H = {y} -/ unfolding G H apply (metis G GH(1) GH(2) H geodesic_segment_between_real ivl_disj_un_two_touch(4) order_trans)
    using \<open>G \<inter> H = {y} -/ unfolding G H
    by (metis (full_types) Un_commute geodesic_segment_between_real geodesic_segment_commute ivl_disj_un_two_touch(4) le_max_iff_disj max.absorb_iff2 max.commute min_absorb2)
qed

context metric_tree begin

/-- We show that a metric tree is uniquely geodesic. -/

subclass uniquely_geodesic_space
proof
  fix x y G H assume H: "geodesic_segment_between G x y" "geodesic_segment_between H x (y::'a)"
  show "G = H"
  proof (rule uniquely_geodesic_spaceI[OF _ H])
    fix G H x y assume "geodesic_segment_between G x y" "geodesic_segment_between H x y" "G \<inter> H = {x, (y::'a)}"
    show "x = y"
    proof (rule ccontr)
      assume "x \<noteq> y"
      then have "dist x y > 0" by auto
      obtain g where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
        by (meson \<open>geodesic_segment_between G x y -/ geodesic_segment_between_def)
      define G2 where "G2 = g`{0..dist x y/2}"
      have "G2 \<subseteq> G" unfolding G2_def g(4) by auto
      define z where "z = g(dist x y/2)"
      have "dist x z = dist x y/2"
        using isometry_onD[OF g(3), of 0 "dist x y/2"] g(1) z_def unfolding dist_real_def by auto
      have "dist y z = dist x y/2"
        using isometry_onD[OF g(3), of "dist x y" "dist x y/2"] g(2) z_def unfolding dist_real_def by auto

      have G2: "geodesic_segment_between G2 x z" unfolding \<open>g 0 = x -/[symmetric] z_def G2_def
        apply (rule geodesic_segmentI2) by (rule isometry_on_subset[OF g(3)], auto simp add: \<open>g 0 = x -/)
      have [simp]: "x ∈ G2" "z ∈ G2" using geodesic_segment_endpoints G2 by auto
      have "dist x a ≤ dist x z" if "a ∈ G2" for a
        apply (rule geodesic_segment_dist_le) using G2 that by auto
      also have "... < dist x y" unfolding \<open>dist x z = dist x y/2 -/ using \<open>dist x y > 0 -/ by auto
      finally have "y \<notin> G2" by auto

      then have "G2 \<inter> H = {x}"
        using \<open>G2 \<subseteq> G -/ \<open>x ∈ G2 -/ \<open>G \<inter> H = {x, y} -/ by auto
      have *: "geodesic_segment_between (G2 ∪ H) z y"
        apply (rule geod_union[of _ _ x])
        using \<open>G2 \<inter> H = {x} -/ \<open>geodesic_segment_between H x y -/ G2 by (auto simp add: geodesic_segment_commute)
      have "dist x y ≤ dist z x + dist x y" by auto
      also have "... = dist z y"
        apply (rule geodesic_segment_dist[OF *]) using \<open>G \<inter> H = {x, y} -/ by auto
      also have "... = dist x y / 2"
        by (simp add: \<open>dist y z = dist x y / 2 -/ metric_space_class.dist_commute)
      finally show False using \<open>dist x y > 0 -/ by auto
    qed
  qed
qed

/-- An important property of metric trees is that any geodesic triangle is degenerate, i.e., the
three sides intersect at a unique point, the center of the triangle, that we introduce now. -/

definition center::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "center x y z = (SOME t. t ∈ {x--y} \<inter> {x--z} \<inter> {y--z})"

lemma center_as_intersection:
  "{x--y} \<inter> {x--z} \<inter> {y--z} = {center x y z}"
proof -
  obtain g where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "{x--y} = g`{0..dist x y}"
    by (meson geodesic_segment_between_def some_geodesic_is_geodesic_segment(1))
  obtain h where h: "h 0 = x" "h (dist x z) = z" "isometry_on {0..dist x z} h" "{x--z} = h`{0..dist x z}"
    by (meson geodesic_segment_between_def some_geodesic_is_geodesic_segment(1))

  define Z where "Z = {t ∈ {0..min (dist x y) (dist x z)}. g t = h t}"
  have "0 ∈ Z" unfolding Z_def using g(1) h(1) by auto
  have [simp]: "closed Z"
  proof -
    have *: "Z = (\<lambda>s. dist (g s) (h s))-`{0} \<inter> {0..min (dist x y) (dist x z)}"
      unfolding Z_def by auto
    show ?thesis
      unfolding * apply (rule closed_vimage_Int)
      using continuous_on_subset[OF isometry_on_continuous[OF g(3)], of "{0..min (dist x y) (dist x z)}"]
            continuous_on_subset[OF isometry_on_continuous[OF h(3)], of "{0..min (dist x y) (dist x z)}"]
            continuous_on_dist by auto
  qed
  define a where "a = Sup Z"
  have "a ∈ Z"
    unfolding a_def apply (rule closed_contains_Sup, auto) using \<open>0 ∈ Z -/ Z_def by auto
  define c where "c = h a"
  then have a: "g a = c" "h a = c" "a \<ge> 0" "a ≤ dist x y" "a ≤ dist x z"
    using \<open>a ∈ Z -/ unfolding Z_def c_def by auto

  define G2 where "G2 = g`{a..dist x y}"
  have G2: "geodesic_segment_between G2 (g a) (g (dist x y))"
    unfolding G2_def apply (rule geodesic_segmentI2)
    using isometry_on_subset[OF g(3)] \<open>a ∈ Z -/ unfolding Z_def by auto
  define H2 where "H2 = h`{a..dist x z}"
  have H2: "geodesic_segment_between H2 (h a) (h (dist x z))"
    unfolding H2_def apply (rule geodesic_segmentI2)
    using isometry_on_subset[OF h(3)] \<open>a ∈ Z -/ unfolding Z_def by auto
  have "G2 \<inter> H2 \<subseteq> {c}"
  proof
    fix w assume w: "w ∈ G2 \<inter> H2"
    obtain sg where sg: "w = g sg" "sg ∈ {a..dist x y}" using w unfolding G2_def by auto
    obtain sh where sh: "w = h sh" "sh ∈ {a..dist x z}" using w unfolding H2_def by auto
    have "dist w x = sg"
      unfolding g(1)[symmetric] sg(1) using isometry_onD[OF g(3), of 0 sg] sg(2)
      unfolding dist_real_def using a by (auto simp add: metric_space_class.dist_commute)
    moreover have "dist w x = sh"
      unfolding h(1)[symmetric] sh(1) using isometry_onD[OF h(3), of 0 sh] sh(2)
      unfolding dist_real_def using a by (auto simp add: metric_space_class.dist_commute)
    ultimately have "sg = sh" by simp
    have "sh ∈ Z" unfolding Z_def using sg sh \<open>a \<ge> 0 -/ unfolding \<open>sg = sh -/ by auto
    then have "sh ≤ a"
      unfolding a_def apply (rule cSup_upper) unfolding Z_def by auto
    then have "sh = a" using sh(2) by auto
    then show "w ∈ {c}" unfolding sh(1) using a(2) by auto
  qed
  then have *: "G2 \<inter> H2 = {c}"
    unfolding G2_def H2_def using a by (auto simp add: image_iff, force)
  have "geodesic_segment_between (G2 ∪ H2) y z"
    apply (subst g(2)[symmetric], subst h(2)[symmetric]) apply(rule geod_union[of _ _ "h a"])
    using geodesic_segment_commute G2 H2 a * by force+
  then have "G2 ∪ H2 = {y--z}"
    using geodesic_segment_unique by auto
  then have "c ∈ {y--z}" using * by auto
  then have *: "c ∈ {x--y} \<inter> {x--z} \<inter> {y--z}"
    using g(4) h(4) c_def a by force
  have center: "center x y z ∈ {x--y} \<inter> {x--z} \<inter> {y--z}"
    unfolding center_def using someI[of "\<lambda>p. p ∈ {x--y} \<inter> {x--z} \<inter> {y--z}", OF *] by blast
  have *: "dist x d = Gromov_product_at x y z" if "d ∈ {x--y} \<inter> {x--z} \<inter> {y--z}" for d
  proof -
    have "dist x y = dist x d + dist d y"
         "dist x z = dist x d + dist d z"
         "dist y z = dist y d + dist d z"
      using that by (auto simp add: geodesic_segment_dist geodesic_segment_unique)
    then show ?thesis unfolding Gromov_product_at_def by (auto simp add: metric_space_class.dist_commute)
  qed
  have "d = center x y z" if "d ∈ {x--y} \<inter> {x--z} \<inter> {y--z}" for d
    apply (rule geodesic_segment_dist_unique[of "{x--y}" x y])
    using *[OF that] *[OF center] that center by auto
  then show "{x--y} \<inter> {x--z} \<inter> {y--z} = {center x y z}" using center by blast
qed

lemma center_on_geodesic [simp]:
  "center x y z ∈ {x--y}"
  "center x y z ∈ {x--z}"
  "center x y z ∈ {y--z}"
  "center x y z ∈ {y--x}"
  "center x y z ∈ {z--x}"
  "center x y z ∈ {z--y}"
using center_as_intersection by (auto simp add: some_geodesic_commute)

lemma center_commute:
  "center x y z = center x z y"
  "center x y z = center y x z"
  "center x y z = center y z x"
  "center x y z = center z x y"
  "center x y z = center z y x"
using center_as_intersection some_geodesic_commute by blast+

lemma center_dist:
  "dist x (center x y z) = Gromov_product_at x y z"
proof -
  have "dist x y = dist x (center x y z) + dist (center x y z) y"
       "dist x z = dist x (center x y z) + dist (center x y z) z"
       "dist y z = dist y (center x y z) + dist (center x y z) z"
    by (auto simp add: geodesic_segment_dist geodesic_segment_unique)
  then show ?thesis unfolding Gromov_product_at_def by (auto simp add: metric_space_class.dist_commute)
qed

lemma geodesic_intersection:
  "{x--y} \<inter> {x--z} = {x--center x y z}"
proof -
  have "{x--y} = {x--center x y z} ∪ {center x y z--y}"
    using center_as_intersection geodesic_segment_split by blast
  moreover have "{x--z} = {x--center x y z} ∪ {center x y z--z}"
    using center_as_intersection geodesic_segment_split by blast
  ultimately have "{x--y} \<inter> {x--z} = {x--center x y z} ∪ ({center x y z--y} \<inter> {x--center x y z}) ∪ ({center x y z--y} \<inter> {x--center x y z}) ∪ ({center x y z--y} \<inter> {center x y z--z})"
    by auto
  moreover have "{center x y z--y} \<inter> {x--center x y z} = {center x y z}"
    using geodesic_segment_split(2) center_as_intersection[of x y z] by auto
  moreover have "{center x y z--y} \<inter> {x--center x y z} = {center x y z}"
    using geodesic_segment_split(2) center_as_intersection[of x y z] by auto
  moreover have "{center x y z--y} \<inter> {center x y z--z} = {center x y z}"
    using geodesic_segment_split(2)[of "center x y z" y z] center_as_intersection[of x y z] by (auto simp add: some_geodesic_commute)
  ultimately show "{x--y} \<inter> {x--z} = {x--center x y z}" by auto
qed
end (*of context metric_tree*)

/-- We can now prove that a metric tree is Gromov hyperbolic, for $\delta = 0$. The simplest
proof goes through the slim triangles property: it suffices to show that, given a geodesic triangle,
there is a point at distance at most $0$ of each of its sides. This is the center we have
constructed above. -/

class metric_tree_with_delta = metric_tree + metric_space_with_deltaG +
  assumes delta0: "deltaG(TYPE('a::metric_space)) = 0"

class Gromov_hyperbolic_space_0 = Gromov_hyperbolic_space +
  assumes delta0 [simp]: "deltaG(TYPE('a::metric_space)) = 0"

class Gromov_hyperbolic_space_0_geodesic = Gromov_hyperbolic_space_0 + geodesic_space

/-- Isabelle does not accept cycles in the class graph. So, we will show that
\verb+metric_tree_with_delta+ is a subclass of \verb+Gromov_hyperbolic_space_0_geodesic+, and
conversely that \verb+Gromov_hyperbolic_space_0_geodesic+ is a subclass of \verb+metric_tree+.

In a tree, we have already proved that triangles are $0$-slim (the center is common to all sides
of the triangle). The $0$-hyperbolicity follows from one of the equivalent characterizations
of hyperbolicity (the other characterizations could be used as well, but the proofs would be
less immediate.) -/

subclass (in metric_tree_with_delta) Gromov_hyperbolic_space_0
proof (standard)
  show "deltaG TYPE('a) = 0" unfolding delta0 by auto
  have "Gromov_hyperbolic_subset (6 * 0) (Set.univ : Set X)"
  proof (rule slim_triangles_implies_hyperbolic)
    fix x::'a and y z Gxy Gyz Gxz
    define w where "w = center x y z"
    assume "geodesic_segment_between Gxy x y"
        "geodesic_segment_between Gxz x z" "geodesic_segment_between Gyz y z"
    then have "Gxy = {x--y}" "Gyz = {y--z}" "Gxz = {x--z}"
      by (auto simp add: local.geodesic_segment_unique)
    then have "w ∈ Gxy" "w ∈ Gyz" "w ∈ Gxz"
      unfolding w_def by auto
    then have "infDist w Gxy ≤ 0 \<and> infDist w Gxz ≤ 0 \<and> infDist w Gyz ≤ 0"
      by auto
    then show "\<exists>w. infDist w Gxy ≤ 0 \<and> infDist w Gxz ≤ 0 \<and> infDist w Gyz ≤ 0"
      by blast
  qed
  then show "Gromov_hyperbolic_subset (deltaG TYPE('a)) (Set.univ : Set X)" unfolding delta0 by auto
qed

/-- To use the fact that reals are Gromov hyperbolic, given that they are a metric tree,
we need to instantiate them as \verb+metric_tree_with_delta+. -/

instantiation real::metric_tree_with_delta
begin
definition deltaG_real::"real itself \<Rightarrow> real"
  where "deltaG_real _ = 0"
instance apply standard unfolding deltaG_real_def by auto
end

/-- Let us now prove the converse: a geodesic space which is $\delta$-hyperbolic for $\delta = 0$
is a metric tree. For the proof, we consider two geodesic segments $G = [x,y]$ and $H = [y,z]$ with a common
endpoint, and we have to show that their union is still a geodesic segment from $x$ to $z$. For
this, introduce a geodesic segment $L = [x,z]$. By the property of thin triangles, $G$ is included
in $H \cup L$. In particular, a point $Y$ close to $y$ but different from $y$ on $G$ is on $L$,
and therefore realizes the equality $d(x,z) = d(x, Y) + d(Y, z)$. Passing to the limit, $y$
also satisfies this equality. The conclusion readily follows thanks to Lemma
\verb+geodesic_segment_union+.
 -/

subclass (in Gromov_hyperbolic_space_0_geodesic) metric_tree
proof
  fix G H x y z assume A: "geodesic_segment_between G x y" "geodesic_segment_between H y z" "G \<inter> H = {y::'a}"
  show "geodesic_segment_between (G ∪ H) x z"
  proof (cases "x = y")
    case True
    then show ?thesis
      by (metis A Un_commute geodesic_segment_between_x_x(3) inf.commute sup_inf_absorb)
  next
    case False
    define D::"nat \<Rightarrow> real" where "D = (\<lambda>n. dist x y - (dist x y) * (1/(real(n+1))))"
    have D: "D n ∈ {0..< dist x y}" "D n ∈ {0..dist x y}" for n
      unfolding D_def by (auto simp add: False divide_simps algebra_simps)
    have Dlim: "D \<longlonglongrightarrow> dist x y - dist x y * 0"
      unfolding D_def by (intro tendsto_intros LIMSEQ_ignore_initial_segment[OF lim_1_over_n, of 1])

    define Y::"nat \<Rightarrow> 'a" where "Y = (\<lambda>n. geodesic_segment_param G x (D n))"
    have *: "Y \<longlonglongrightarrow> y"
      unfolding Y_def apply (subst geodesic_segment_param(2)[OF A(1), symmetric])
      using isometry_on_continuous[OF geodesic_segment_param(4)[OF A(1)]]
      unfolding continuous_on_sequentially comp_def using D(2) Dlim by auto

    have "dist x z = dist x (Y n) + dist (Y n) z" for n
    proof -
      obtain L where L: "geodesic_segment_between L x z" using geodesic_subsetD[OF geodesic] by blast
      have "Y n ∈ G" unfolding Y_def
        apply (rule geodesic_segment_param(3)[OF A(1)]) using D[of n] by auto
      have "dist x (Y n) = D n"
        unfolding Y_def apply (rule geodesic_segment_param[OF A(1)]) using D[of n] by auto
      then have "Y n \<noteq> y"
        using D[of n] by auto
      then have "Y n \<notin> H" using A(3) \<open>Y n ∈ G -/ by auto
      have "infDist (Y n) (H ∪ L) ≤ 4 * δ"
        apply (rule thin_triangles[OF geodesic_segment_commute[OF A(2)] geodesic_segment_commute[OF L] geodesic_segment_commute[OF A(1)]])
        using \<open>Y n ∈ G -/ by simp
      then have "infDist (Y n) (H ∪ L) = 0"
        using infDist_nonneg[of "Y n" "H ∪ L"] unfolding delta0 by auto
      have "Y n ∈ H ∪ L"
      proof (subst in_closed_iff_infDist_zero)
        have "closed H"
          using A(2) geodesic_segment_topology geodesic_segment_def by fastforce
        moreover have "closed L"
          using L geodesic_segment_topology geodesic_segment_def by fastforce
        ultimately show "closed (H ∪ L)" by auto
        show "H ∪ L \<noteq> {}" using A(2) geodesic_segment_endpoints(1) by auto
      qed (fact)
      then have "Y n ∈ L" using \<open>Y n \<notin> H -/ by simp
      show ?thesis using geodesic_segment_dist[OF L \<open>Y n ∈ L -/] by simp
    qed
    moreover have "(\<lambda>n. dist x (Y n) + dist (Y n) z) \<longlonglongrightarrow> dist x y + dist y z"
      by (intro tendsto_intros *)
    ultimately have "(\<lambda>n. dist x z) \<longlonglongrightarrow> dist x y + dist y z"
      using filterlim_cong eventually_sequentially by auto
    then have *: "dist x z = dist x y + dist y z"
      using LIMSEQ_unique by auto
    show "geodesic_segment_between (G ∪ H) x z"
      by (rule geodesic_segment_union[OF * A(1) A(2)])
  qed
qed

end (*of theory Gromov_Hyperbolic*)
