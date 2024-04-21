/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD -/
import GromovHyperbolicity.GromovHyperbolic.Basic
import Mathlib.Tactic.Peel

-- imports "HOL-Decision_Procs.Approximation"
-- hide_const (open) Approximation.Min
-- hide_const (open) Approximation.Max

/-! # Quasiconvexity -/

open Metric Set

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
  apply quasiconvexI
  · simp
  intro x y hx hy
  obtain ⟨H, hHG, hHxy⟩ : ∃ H, H ⊆ G ∧ geodesic_segment_between H x y := sorry
--     using `geodesic_subsegment_exists` [OF assms(1) *] by auto
  refine ⟨H, hHxy, ?_⟩
  intro _ _
  rw [infDist_zero_of_mem]
  aesop

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

local notation "δ" => Gromov_hyperbolic_space.deltaG M

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
to $x$ go close to $p$, i.e., the triangular inequality $d(x,y) ≤ d(x,p) + d(p,y)$ is essentially
an equality, up to an additive constant. -/
lemma dist_along_quasiconvex (hCG : quasiconvex C G) (hp : p ∈ proj_set x G) (hy : y ∈ G) :
    dist x p + dist p y ≤ dist x y + 4 * δ + 2 * C := by
  have : p ∈ G := proj_setD hp
  obtain ⟨H, hH₁, hH₂⟩ : ∃ H, geodesic_segment_between H p y ∧ ∀ q ∈ H, infDist q G ≤ C :=
    quasiconvexD hCG this hy
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m ∈ H, infDist x H = dist x m := sorry
--     apply (rule `infDist_proper_attained` [of H x]) using `geodesic_segment_topology` [OF geodesic_segmentI[OF H(1)]] by auto
  have I : dist x m ≤ Gromov_product_at x p y + 2 * δ := by
    rw [← hm₂]
    apply infDist_triangle_side x hH₁
  have : ∀ e > 0, dist x p - dist x m - C ≤ e := by
    intro e he
    obtain ⟨r, hrG, hrm⟩ : ∃ r ∈ G, dist m r < infDist m G + e := sorry
--       apply (rule `infDist_almost_attained`) using he assms(3) by auto
    have : infDist m G ≤ C := hH₂ _ hm₁
    have :=
    calc dist x p ≤ dist x r := sorry -- using hrG assms(2) `proj_set_dist_le` by blast
      _ ≤ dist x m + dist m r := dist_triangle ..
--     finally show ?thesis using * by (auto simp add: metric_space_class.dist_commute)
    linarith
  have : dist x p - dist x m - C ≤ 0 := le_of_forall_le_of_dense this
  rw [Gromov_product_at] at I
  linarith
--   then show ?thesis
--     using I unfolding Gromov_product_at_def by (auto simp add: algebra_simps divide_simps)
-- qed

/-- The next lemma is~\<^cite> Proposition 10.2.1 in "coornaert_delzant_papadopoulos" with better
constants. It states that the distance between the projections
on a quasi-convex set is controlled by the distance of the original points, with a gain given by the
distances of the points to the set. -/
-- **Lemma 2.4**
lemma proj_along_quasiconvex_contraction (h : quasiconvex C G) (hx : px ∈ proj_set x G)
    (hy : py ∈ proj_set y G) :
    dist px py ≤ max (5 * δ + 2 * C) (dist x y - dist px x - dist py y + 10 * δ + 4 * C) := by
  have := dist_along_quasiconvex h hx <| proj_setD hy
  have := dist_along_quasiconvex h hy <| proj_setD hx
  have := Gromov_hyperbolic_space.hyperb_quad_ineq x py y px
  simp only [dist_comm] at *
  obtain _ | _ := max_cases (5 * δ + 2 * C) (dist x y - dist px x - dist py y + 10 * δ + 4 * C) <;>
  obtain _ | _ := max_cases (dist x y + dist px py) (dist px x + dist py y) <;>
  linarith

/-- The projection on a quasi-convex set is $1$-Lipschitz up to an additive error. -/
lemma proj_along_quasiconvex_contraction' (h : quasiconvex C G) (hx : px ∈ proj_set x G)
    (hy : py ∈ proj_set y G) :
    dist px py ≤ dist x y + 4 * δ + 2 * C := by
  have := dist_along_quasiconvex h hx <| proj_setD hy
  have := dist_along_quasiconvex h hy <| proj_setD hx
  have := dist_triangle x y py
  have := dist_triangle y x px
  simp only [dist_comm] at *
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

open Topology

/-- If one projects a continuous curve on a quasi-convex set, the image does not have to be
connected (the projection is discontinuous), but since the projections of nearby points are within
uniformly bounded distance one can find in the projection a point with almost prescribed distance
to the starting point, say. For further applications, we also pick the first such point, i.e.,
all the previous points are also close to the starting point. -/
-- **Lemma 2.2** in article.
-- not sure whether inequalities are sharp or non-sharp
lemma quasi_convex_projection_small_gaps {f p : ℝ → M} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hab : a ≤ b)
    (h : quasiconvex C G)
    (hfG : ∀ t ∈ Icc a b, p t ∈ proj_set (f t) G)
    (hdelta : delta > δ)
    (hd : d ∈ Icc (4 * delta + 2 * C) (dist (p a) (p b))) :
    ∃ t ∈ Icc a b, dist (p a) (p t) ∈ Icc (d - 4 * delta - 2 * C) d
                    ∧ ∀ s ∈ Icc a t, dist (p a) (p s) ≤ d := by
  have : Inhabited M := ⟨f 0⟩
  have : 0 ≤ δ := delta_nonneg M
  have : 0 ≤ C := quasiconvexC h
  have hd0 : 0 ≤ d := by linarith [hd.1]

/- The idea is to define the desired point as the last point `u` for which there is a projection
at distance at most `d` of the starting point. Then the projection can not be much closer to
the starting point, or one could point another such point further away by almost continuity, giving
a contradiction. The technical implementation requires some care, as the "last point" may not
satisfy the property, for lack of continuity. If it does, then fine. Otherwise, one should go just
a little bit to its left to find the desired point. -/
  obtain ⟨u, ⟨hau, hub⟩, A, H3⟩ : ∃ u ∈ Icc a b, (∀ s ∈ Ico a u, dist (p a) (p s) ≤ d)
      ∧ (u < b → ∃ᶠ s in 𝓝[≥] u, ¬ dist (p a) (p s) ≤ d) :=
    method_of_continuity hab (P := fun s ↦ dist (p a) (p s) ≤ d) (by simpa)

  have hf2 : ContinuousWithinAt f (Icc a b) u := hf.continuousWithinAt ⟨hau, hub⟩
  have hdeltaδ : 0 < delta - δ := by linarith
  have H1 : ∀ᶠ s in 𝓝[Icc a b] u, dist (f s) (f u) < delta - δ :=
    hf2.tendsto <| ball_mem_nhds (f u) hdeltaδ

  by_cases hdp : dist (p a) (p u) > d
/- First, consider the case where `u` does not satisfy the defining property. Then the
desired point `t` is taken slightly to its left. -/
  · obtain ⟨t, ⟨hta, htu⟩, htue0⟩ : ∃ t ∈ Ico a u, dist (f t) (f u) < delta - δ := by
      have hau : a < u := lt_of_le_of_ne hau <| by rintro rfl; linarith [dist_self (p a)]
      have : (𝓝[<] u).NeBot := nhdsWithin_Iio_self_neBot _
      have H2 : ∀ᶠ s in 𝓝[<] u, s ∈ Ico a u := Ico_mem_nhdsWithin_Iio' hau
      have : Ico a u ⊆ Icc a b := Ico_subset_Icc_self.trans <| Icc_subset_Icc_right hub
      have := H1.filter_mono (nhdsWithin_mono _ this)
      rw [nhdsWithin_Ico_eq_nhdsWithin_Iio hau] at this
      exact (H2.and this).exists

    have htab : t ∈ Icc a b := ⟨hta, htu.le.trans hub⟩
    refine ⟨t, htab, ?_⟩

    have H1 : ∀ s ∈ Icc a t, dist (p a) (p s) ≤ d := by
      intro s hs
      exact A s ⟨hs.1, trans hs.2 htu⟩

    refine ⟨⟨?_, H1 _ ?_⟩, H1⟩
    · have : dist (p t) (p u) ≤ dist (f t) (f u) + 4 * δ + 2 * C :=
            proj_along_quasiconvex_contraction' h (hfG t htab) (hfG u ⟨hau, hub⟩)
      have : dist (p a) (p u)  ≤ dist (p a) (p t) + dist (p t) (p u) := dist_triangle ..
      linarith
    · rwa [right_mem_Icc]
/- Next, consider the case where `u` satisfies the defining property. Then we will take `t = u`.
The only nontrivial point to check is that the distance of `f u` to the starting point is not
too small. For this, we need to separate the case where `u = b` (in which case one argues directly)
and the case where `u < b`, where one can use a point slightly to the right of `u` which has a
projection at distance > `d` of the starting point, and use almost continuity. -/
  · push_neg at hdp H3
    have B : ∀ s ∈ Icc a u, dist (p a) (p s) ≤ d := by
      intro s hs
      obtain rfl | hsu := eq_or_lt_of_le hs.2
      · exact hdp
      · exact A _ ⟨hs.1, hsu⟩
    have huau : u ∈ Icc a u := by rwa [right_mem_Icc]
    refine ⟨u, ⟨hau, hub⟩, ⟨?_, B _ huau⟩, B⟩
    obtain rfl | hub := eq_or_lt_of_le hub
    · linarith [hd.2]
    obtain ⟨w, hwp, ⟨hwu, hwb⟩, hwf⟩ :
        ∃ w, d < dist (p a) (p w) ∧ w ∈ Icc u b ∧ dist (f w) (f u) < delta - δ := by
      have : (𝓝[≥] u).NeBot := nhdsWithin_Ici_self_neBot u
      have H2 : ∀ᶠ s in 𝓝[≥] u, s ∈ Icc u b := Icc_mem_nhdsWithin_Ici' hub
      have : Icc u b ⊆ Icc a b := Icc_subset_Icc_left hau
      have := H1.filter_mono (nhdsWithin_mono _ this)
      rw [nhdsWithin_Icc_eq_nhdsWithin_Ici hub] at this
      exact (H3 hub).and_eventually (H2.and this) |>.exists
    rw [dist_comm] at hwf
    have : dist (p u) (p w) ≤ dist (f u) (f w) + 4 * δ + 2 * C := by
      apply proj_along_quasiconvex_contraction' h (hfG _ ⟨hau, hub.le⟩) (hfG _ _)
      exact ⟨hau.trans hwu, hwb⟩
    have : dist (p a) (p w) ≤ dist (p a) (p u) + dist (p u) (p w) := dist_triangle ..
    linarith

-- FIXME decide whether this should be global
attribute [simp] le_neg neg_le

/-- Same lemma, except that one exchanges the roles of the beginning and the end point. -/
-- not sure whether inequalities are sharp or non-sharp
lemma quasi_convex_projection_small_gaps' {f p : ℝ → M} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hab : a ≤ b)
    (h : quasiconvex C G)
    (hfG : ∀ t ∈ Icc a b, p t ∈ proj_set (f t) G)
    (hdelta : delta > δ)
    (hd : d ∈ Icc (4 * delta + 2 * C) (dist (p a) (p b))) :
    ∃ t ∈ Icc a b, (dist (p b) (p t) ∈ Icc (d - 4 * delta - 2 * C) d)
                    ∧ (∀ s ∈ Icc t b, dist (p b) (p s) ≤ d) := by
  have hf_neg : ContinuousOn (fun t : ℝ => f (- t)) (Icc (-b) (-a)) := by
    refine hf.comp continuousOn_neg ?_
    aesop (add norm unfold MapsTo)
  let q := fun t ↦ p (-t)
  obtain ⟨t, htab, htq, htq'⟩ :
      ∃ t ∈ Icc (-b) (-a), dist (q (-b)) (q t) ∈ Icc (d - 4 * delta - 2 * C) d
                    ∧ ∀ s ∈ Icc (-b) t, dist (q (-b)) (q s) ≤ d := by
    refine quasi_convex_projection_small_gaps hf_neg ?_ h ?_ hdelta ?_ <;>
    aesop (add norm [dist_comm])
  refine ⟨-t, ?_, ?_, ?_⟩
  · aesop
  · simpa using htq
  · intro s hs
    convert htq' (-s) _ using 2 <;>
    aesop
