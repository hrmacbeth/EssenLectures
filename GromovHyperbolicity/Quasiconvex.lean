/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD -/
import GromovHyperbolicity.GromovHyperbolic
import Mathlib.Tactic.Peel

/-! # Quasiconvexity -/

open Metric Set Classical

variable {M : Type*} [MetricSpace M]

/-- In a Gromov-hyperbolic setting, convexity is not a well-defined notion as everything should
be coarse. The good replacement is quasi-convexity: A set `x` is `C`-quasi-convex if any pair of
points in `x` can be joined by a geodesic that remains within distance `C` of `x`. One could also
require this for all geodesics, up to changing `C`, as two geodesics between the same endpoints
remain within uniformly bounded distance. We use the first definition to ensure that a geodesic is
0-quasi-convex. -/
structure Quasiconvex (C : ℝ) (X : Set M) : Prop :=
  (C_nonneg : 0 ≤ C)
  (exists_nearby_geodesic {x y : M} (_ : x ∈ X) (_ : y ∈ X) :
    ∃ G, GeodesicSegmentBetween G x y ∧ (∀ z ∈ G, infDist z X ≤ C))

variable {C D : ℝ} {X G : Set M}

lemma GeodesicSegment.quasiconvex {G : Set M} (hG : GeodesicSegment G) : Quasiconvex 0 G where
  C_nonneg := by simp
  exists_nearby_geodesic {x y} (hx hy) := by
    obtain ⟨H, hHG, hHxy⟩ := geodesic_subsegment_exists hG hx hy
    refine ⟨H, hHxy, ?_⟩
    intro _ _
    rw [infDist_zero_of_mem]
    aesop

lemma quasiconvex_empty (hC : C ≥ 0) : Quasiconvex C (∅ : Set M) where
  C_nonneg := by aesop
  exists_nearby_geodesic := by aesop

lemma Quasiconvex.mono (hCD : C ≤ D) (hC : Quasiconvex C G) : Quasiconvex D G where
  C_nonneg := by linarith [hC.C_nonneg]
  exists_nearby_geodesic {x y} (hx hy) := by
    peel hC.exists_nearby_geodesic hx hy
    linarith

variable [GromovHyperbolicSpace M] [GeodesicSpace M]

local notation "δ" => GromovHyperbolicSpace.deltaG M

/-- The `r`-neighborhood of a quasi-convex set is still quasi-convex in a hyperbolic space,
for a constant that does not depend on `r`. -/
lemma Quasiconvex.cthickening [Inhabited M] (h : Quasiconvex C X) {r : ℝ} (hr : r ≥ 0) :
    Quasiconvex (C + 8 * δ) (cthickening r X) where
  C_nonneg := by
    have := h.C_nonneg
    have := delta_nonneg M
    positivity
  exists_nearby_geodesic {y z} (hy hz) := by
    refine ⟨{y‒z}, sorry, ?_⟩
    sorry

/-- If `x` has a projection `p` on a quasi-convex set `G`, then all segments from a point in `G`
to `x` go close to `p`, i.e., the triangular inequality $d(x,y) ≤ d(x,p) + d(p,y)$ is essentially
an equality, up to an additive constant. -/
lemma dist_along_quasiconvex (hCG : Quasiconvex C G) {p x : M} (hp : p ∈ projSet x G) {y : M} (hy : y ∈ G) :
    dist x p + dist p y ≤ dist x y + 4 * δ + 2 * C := by
  have : p ∈ G := hp.1
  obtain ⟨H, hH₁, hH₂⟩ : ∃ H, GeodesicSegmentBetween H p y ∧ ∀ q ∈ H, infDist q G ≤ C :=
    hCG.exists_nearby_geodesic this hy
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m ∈ H, infDist x H = dist x m :=
    hH₁.isCompact.exists_infDist_eq_dist hH₁.nonempty _
  have I : dist x m ≤ gromovProductAt x p y + 2 * δ := by
    rw [← hm₂]
    apply infDist_triangle_side x hH₁
  have : ∀ e > 0, dist x p - dist x m - C ≤ e := by
    intro e he
    obtain ⟨r, hrG, hrm⟩ : ∃ r ∈ G, dist m r < infDist m G + e := by
      rw [← infDist_lt_iff]
      · linarith
      · exact ⟨_, hy⟩
    have : infDist m G ≤ C := hH₂ _ hm₁
    have :=
    calc dist x p ≤ dist x r := projSet_dist_le hrG hp
      _ ≤ dist x m + dist m r := dist_triangle ..
--     finally show ?thesis using * by (auto simp add: metric_space_class.dist_commute)
    linarith
  have : dist x p - dist x m - C ≤ 0 := le_of_forall_le_of_dense this
  rw [gromovProductAt] at I
  linarith
--   then show ?thesis
--     using I unfolding gromovProductAt_def by (auto simp add: algebra_simps divide_simps)
-- qed

/-- The next lemma is~\<^cite> Proposition 10.2.1 in "coornaert_delzant_papadopoulos" with better
constants. It states that the distance between the projections
on a quasi-convex set is controlled by the distance of the original points, with a gain given by the
distances of the points to the set. -/
-- **Lemma 2.4**
lemma proj_along_quasiconvex_contraction (h : Quasiconvex C G) {px x : M} (hx : px ∈ projSet x G)
    {py y : M} (hy : py ∈ projSet y G) :
    dist px py ≤ max (5 * δ + 2 * C) (dist x y - dist px x - dist py y + 10 * δ + 4 * C) := by
  have := dist_along_quasiconvex h hx <| hy.1
  have := dist_along_quasiconvex h hy <| hx.1
  have := GromovHyperbolicSpace.hyperb_quad_ineq x py y px
  simp only [dist_comm] at *
  obtain _ | _ := max_cases (5 * δ + 2 * C) (dist x y - dist px x - dist py y + 10 * δ + 4 * C) <;>
  obtain _ | _ := max_cases (dist x y + dist px py) (dist px x + dist py y) <;>
  linarith

/-- The projection on a quasi-convex set is 1-Lipschitz up to an additive error. -/
lemma proj_along_quasiconvex_contraction' (h : Quasiconvex C G) {px x : M} (hx : px ∈ projSet x G)
    {py y : M} (hy : py ∈ projSet y G) :
    dist px py ≤ dist x y + 4 * δ + 2 * C := by
  have := dist_along_quasiconvex h hx <| hy.1
  have := dist_along_quasiconvex h hy <| hx.1
  have := dist_triangle x y py
  have := dist_triangle y x px
  simp only [dist_comm] at *
  linarith

/-- We can in particular specialize the previous statements to geodesics, which are
0-quasi-convex. -/
lemma dist_along_geodesic (h : GeodesicSegment G) {p x : M} (hx : p ∈ projSet x G) {y : M} (hy : y ∈ G) :
    dist x p + dist p y ≤ dist x y + 4 * δ := by
  have H := dist_along_quasiconvex h.quasiconvex hx hy
  ring_nf at H ⊢
  exact H

lemma proj_along_geodesic_contraction (h : GeodesicSegment G) {px x : M} (hx : px ∈ projSet x G)
    {py y : M} (hy : py ∈ projSet y G) :
    dist px py ≤ max (5 * δ) (dist x y - dist px x - dist py y + 10 * δ) := by
  have H := proj_along_quasiconvex_contraction h.quasiconvex hx hy
  ring_nf at H ⊢
  exact H

lemma proj_along_geodesic_contraction' (h : GeodesicSegment G) {px x : M} (hx : px ∈ projSet x G)
    {py y : M} (hy : py ∈ projSet y G) :
    dist px py ≤ dist x y + 4 * δ := by
  have H := proj_along_quasiconvex_contraction' h.quasiconvex hx hy
  ring_nf at H ⊢
  exact H

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
    (h : Quasiconvex C G)
    (hfG : ∀ t ∈ Icc a b, p t ∈ projSet (f t) G)
    {delta : ℝ} (hdelta : delta > δ)
    {d : ℝ} (hd : d ∈ Icc (4 * delta + 2 * C) (dist (p a) (p b))) :
    ∃ t ∈ Icc a b, dist (p a) (p t) ∈ Icc (d - 4 * delta - 2 * C) d
                    ∧ ∀ s ∈ Icc a t, dist (p a) (p s) ≤ d := by
  have : Inhabited M := ⟨f 0⟩
  have : 0 ≤ δ := delta_nonneg M
  have : 0 ≤ C := h.C_nonneg
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
    (h : Quasiconvex C G)
    (hfG : ∀ t ∈ Icc a b, p t ∈ projSet (f t) G)
    {delta : ℝ} (hdelta : delta > δ)
    {d : ℝ} (hd : d ∈ Icc (4 * delta + 2 * C) (dist (p a) (p b))) :
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
  · simpa [q] using htq
  · intro s hs
    convert htq' (-s) _ using 2 <;>
    aesop
