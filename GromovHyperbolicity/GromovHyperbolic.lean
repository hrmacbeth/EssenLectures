/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD -/
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.MetricSpace.HausdorffDistance
import GromovHyperbolicity.Prereqs.GeodesicSpace
import GromovHyperbolicity.Prereqs.Misc

/-!
# Gromov hyperbolic spaces
-/

open Metric Set Classical
attribute [gcongr] infDist_le_infDist_of_subset -- FIXME move this

noncomputable section

/-! ## Definition, basic properties

Although we will mainly work with type classes later on, we introduce the definition
of hyperbolicity on subsets of a metric space.

Two important references on this topic are~\<^cite>"ghys_hyperbolique" and~\<^cite> "bridson_haefliger".
We will sometimes follow them, sometimes depart from them.
-/

section
variable {X : Type*} [MetricSpace X]

/--
A set is δ-hyperbolic if it satisfies the following inequality. It is very obscure at first sight,
but we will see several equivalent characterizations later on. For instance, a space is hyperbolic
(maybe for a different constant δ) if all geodesic triangles are thin, i.e., every side is
close to the union of the two other sides. This definition captures the main features of negative
curvature at a large scale, and has proved extremely fruitful and influential. -/
def GromovHyperbolic (δ : ℝ) (A : Set X) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, ∀ t ∈ A,
  dist x y + dist z t ≤ max (dist x z + dist y t) (dist x t + dist y z) + 2 * δ

variable {δ : ℝ} {A : Set X}

/-- When the four points are not all distinct, the above inequality is always satisfied for δ = 0.-/
lemma GromovHyperbolic_ineq_not_distinct {x y z t : X}
    (h : x = y ∨ x = z ∨ x = t ∨ y = z ∨ y = t ∨ z = t) :
    dist x y + dist z t ≤ max (dist x z + dist y t) (dist x t + dist y z) := by
  have := dist_triangle z x t
  have := dist_triangle x z y
  aesop (add simp [dist_comm, add_comm])

/-- It readily follows from the definition that hyperbolicity passes to the closure of the set. -/
lemma GromovHyperbolic_closure (h : GromovHyperbolic δ A) :
    GromovHyperbolic δ (closure A) := by
  let f : X × X × X × X → ℝ := fun p ↦ dist p.1 p.2.1 + dist p.2.2.1 p.2.2.2
  -- after `fun_prop` bugfix go back to
  -- let f : X × X × X × X → ℝ := fun (x, y, z, t) ↦ dist x y + dist z t
  have hf : Continuous f := by fun_prop
  let g : X × X × X × X → ℝ := fun p ↦
    max (dist p.1 p.2.2.1 + dist p.2.1 p.2.2.2) (dist p.1 p.2.2.2 + dist p.2.1 p.2.2.1) + 2 * δ
  -- let g : X × X × X × X → ℝ :=
  --   fun (x, y, z, t) ↦ max (dist x z + dist y t) (dist x t + dist y z) + 2 * δ
  have hg : Continuous g := by fun_prop
  intro x hx y hy z hz t ht
  have hxyzt : (x, y, z, t) ∈ closure (A ×ˢ (A ×ˢ (A ×ˢ A))) := by
    simp only [closure_prod_eq, Set.mem_prod]
    tauto
  refine le_on_closure (f := f) (g := g) ?_ hf.continuousOn hg.continuousOn hxyzt
  rintro ⟨x, y, z, t⟩ ⟨hx, hy, hz, ht⟩
  exact h x hx y hy z hz t ht

/-! ## The Gromov product -/

/-- A good formulation of hyperbolicity will be in terms of Gromov products. Intuitively, the
Gromov product of `x` and `y` based at `e` is the distance between `e` and the geodesic between
`x` and `y`. It is also the time after which the geodesics from `e` to `x` and from `e` to `y`
stop travelling together. -/
def gromovProductAt (e x y : X) : ℝ := (dist e x + dist e y - dist x y) / 2

@[simp] lemma gromovProductAt_nonneg (e x y : X) : gromovProductAt e x y ≥ 0 := by
  have := dist_triangle x e y
  simp only [gromovProductAt, ge_iff_le]
  cancel_denoms
  simpa [dist_comm, add_comm] using this

lemma gromovProductAt_commute (e x y : X) : gromovProductAt e x y = gromovProductAt e y x := by
  simp only [gromovProductAt, dist_comm, add_comm]

@[simp] lemma gromovProductAt_le_dist (e x y : X) :
    gromovProductAt e x y ≤ dist e x ∧ gromovProductAt e x y ≤ dist e y := by
  have := dist_triangle e x y
  have := dist_triangle e y x
  simp only [gromovProductAt, dist_comm] at *
  constructor <;> linarith

lemma gromovProductAt_le_infDist {x y : X} {G : Set X} (h : GeodesicSegmentBetween G x y) {e : X} :
    gromovProductAt e x y ≤ infDist e G := by
  rw [infDist_eq_iInf]
  have : Nonempty G := h.nonempty.to_subtype
  apply le_ciInf
  rintro ⟨z, hz⟩
  dsimp [gromovProductAt]
  have := dist_triangle e z x
  have := dist_triangle e z y
  have := h.dist_eq hz
  simp only [dist_comm] at *
  linarith

lemma gromovProductAt_add (e x y : X) :
    gromovProductAt e x y + gromovProductAt x e y = dist e x := by
  simp only [gromovProductAt, dist_comm]
  ring

lemma gromovProductAt_geodesic_segment {x y : X} {G : Set X}
    (h : GeodesicSegmentBetween G x y) {t : ℝ} (ht₀ : 0 ≤ t) (ht : t ≤ dist x y) :
    gromovProductAt x y (G.param x t) = t := by
  have : dist x (G.param x t) = t := h.param6 ⟨ht₀, ht⟩
  have :
      dist x (G.param x t) + dist (G.param x t) y = dist x y := by
    apply h.dist_eq
    exact h.param3 ⟨ht₀, ht⟩
  dsimp [gromovProductAt]
  simp only [dist_comm] at *
  linarith

@[simp] lemma gromovProductAt_e_x_x (e x : X) : gromovProductAt e x x = dist e x := by
  simp [gromovProductAt]

/-- The Gromov product is continuous in its three variables. -/
-- never used?
@[fun_prop] lemma gromovProductAt_continuous :
    Continuous (fun (p : X × X × X) ↦ gromovProductAt p.1 p.2.1 p.2.2) := by
  simp only [gromovProductAt]
  fun_prop (disch := norm_num)

end

/-! ## Typeclass for Gromov hyperbolic spaces

We could (should?) just derive `GromovHyperbolicSpace` from `MetricSpace`.
However, in this case, properties of metric spaces are not available when working in the locale!
It is more efficient to ensure that we have a metric space by putting a type class restriction
in the definition. The δ in Gromov-hyperbolicity type class is called `deltaG` to
avoid name clashes. -/

class GromovHyperbolicSpace (X : Type*) [MetricSpace X] where
  deltaG : ℝ
  hyperb_quad_ineq0 : GromovHyperbolic deltaG (Set.univ : Set X)

variable {X : Type*} [MetricSpace X] [GromovHyperbolicSpace X]

local notation "δ" => GromovHyperbolicSpace.deltaG X

lemma GromovHyperbolicSpace.hyperb_quad_ineq (x y z t : X) :
    dist x y + dist z t ≤ max (dist x z + dist y t) (dist x t + dist y z) + 2 * δ := by
  apply GromovHyperbolicSpace.hyperb_quad_ineq0 <;> aesop

/-- It readily follows from the definition that the completion of a δ-hyperbolic
space is still δ-hyperbolic. -/
instance deltaG_metric_completion : GromovHyperbolicSpace (UniformSpace.Completion X) where
  deltaG := δ
  hyperb_quad_ineq0 := by
    intro x hx y hy z hz t ht
    simp only [Set.mem_univ] at *
    induction x, y, z, t using UniformSpace.Completion.induction_on₄
    · apply isClosed_le <;> fun_prop
    · simp only [UniformSpace.Completion.dist_eq]
      apply GromovHyperbolicSpace.hyperb_quad_ineq

open GromovHyperbolicSpace

variable (X) in -- TODO `positivity` attribute
@[simp] lemma delta_nonneg [Inhabited X] : δ ≥ 0 := by
  let x : X := default
  have := hyperb_quad_ineq x x x x
  aesop

lemma hyperb_ineq (e x y z : X) :
    gromovProductAt e x z ≥ min (gromovProductAt e x y) (gromovProductAt e y z) - δ := by
  have H := hyperb_quad_ineq e y x z
  simp only [gromovProductAt, dist_comm, ← max_add_add_right, ← min_sub_sub_right,
    le_max_iff, min_le_iff] at *
  refine Or.elim H (fun _ => Or.inr ?_) (fun _ => Or.inl ?_) <;>
  · cancel_denoms
    rw [← sub_nonpos] at *
    abel_nf at *
    assumption

lemma hyperb_ineq' (e x y z : X) :
    gromovProductAt e x z + δ ≥ min (gromovProductAt e x y) (gromovProductAt e y z) := by
  have := hyperb_ineq e x y z
  aesop

lemma hyperb_ineq_4_points (e x y z t : X) :
    min (gromovProductAt e x y) (min (gromovProductAt e y z) (gromovProductAt e z t)) - 2 * δ
    ≤ gromovProductAt e x t := by
  have : Inhabited X := ⟨e⟩
  have h1 := hyperb_ineq e x y z
  have h2 := hyperb_ineq e x z t
  have := delta_nonneg X
  simp only [← min_sub_sub_right, min_le_iff] at *
  by_contra!
  obtain h1a | h1b := h1 <;> obtain h2a | h2b := h2 <;> linarith

lemma hyperb_ineq_4_points' (e x y z t : X) :
    min (gromovProductAt e x y) (min (gromovProductAt e y z) (gromovProductAt e z t))
    ≤ gromovProductAt e x t + 2 * δ := by
  have := hyperb_ineq_4_points e x y z t
  aesop

/-- In Gromov-hyperbolic spaces, geodesic triangles are thin, i.e., a point on one side of a
geodesic triangle is close to the union of the two other sides (where the constant in "close"
is `4 * δ`, independent of the size of the triangle). We prove this basic property
(which, in fact, is a characterization of Gromov-hyperbolic spaces: a geodesic space in which
triangles are thin is hyperbolic). -/
lemma thin_triangles1 {x y z : X} {G : Set X}
    (hxy : GeodesicSegmentBetween G x y) {H : Set X} (hxz : GeodesicSegmentBetween H x z)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht : t ≤ gromovProductAt x y z) :
    dist (G.param x t) (H.param x t) ≤ 4 * δ := by
  have : Inhabited X := ⟨x⟩
  have h1 : gromovProductAt x z (H.param x t) = t := by
    apply gromovProductAt_geodesic_segment hxz ht₀
    have := gromovProductAt_le_dist x y z
    linarith
  have : min (gromovProductAt x y z) (gromovProductAt x z (H.param x t)) - δ
      ≤ gromovProductAt x y (H.param x t) := hyperb_ineq ..
  have I : t - δ ≤ gromovProductAt x y (H.param x t) := by
    rwa [h1, min_eq_right ht] at this
  have h2 : gromovProductAt x (G.param x t) y = t := by
    rw [gromovProductAt_commute]
    apply gromovProductAt_geodesic_segment hxy ht₀
    have := gromovProductAt_le_dist x y z
    linarith
  have I :=
  calc t - 2 * δ = min t (t- δ) - δ := by
        rw [min_eq_right]
        · ring
        · have : 0 ≤ δ := delta_nonneg X
          linarith
    _ ≤ min (gromovProductAt x (G.param x t) y)
          (gromovProductAt x y (H.param x t)) - δ := by
        rw [h2]
        gcongr
    _ ≤ gromovProductAt x (G.param x t) (H.param x t) :=
        hyperb_ineq ..
  have A : dist x (G.param x t) = t := by
    refine hxy.param6 ⟨ht₀, ?_⟩
    calc t ≤ _ := ht
      _ ≤ _ := (gromovProductAt_le_dist _ _ _).1
  have B : dist x (H.param x t) = t := by
    refine hxz.param6 ⟨ht₀, ?_⟩
    calc t ≤ _ := ht
      _ ≤ _ := (gromovProductAt_le_dist _ _ _).2
  rw [gromovProductAt] at I
  linarith

theorem thin_triangles {x y z w : X}
    {Gxy : Set X} (hxy : GeodesicSegmentBetween Gxy x y)
    {Gxz : Set X} (hxz : GeodesicSegmentBetween Gxz x z)
    {Gyz : Set X} (hyz : GeodesicSegmentBetween Gyz y z)
    (hw : w ∈ Gyz) :
    infDist w (Gxy ∪ Gxz) ≤ 4 * δ := by
  obtain ⟨t, ht0, htw⟩ : ∃ t ∈ Icc 0 (dist y z), w = Gyz.param y t := by
    rw [← hyz.param5] at hw
    obtain ⟨t, ht, htw⟩ := hw
    exact ⟨t, ht, htw.symm⟩
  by_cases ht : t ≤ gromovProductAt y x z
  · have : dist w (Gxy.param y t) ≤ 4 * δ := by
      rw [htw]
      refine thin_triangles1 hyz (z := x) hxy.symm ht0.1 ?_
      rwa [gromovProductAt_commute]
    refine le_trans ?_ this
    apply infDist_le_dist_of_mem
    apply mem_union_left
    refine hxy.symm.param3 ⟨ht0.1, ?_⟩
    calc t ≤ _ := ht
      _ ≤ _ := (gromovProductAt_le_dist _ _ _).1
  · let s := dist y z - t
    have hs : s ∈ Ico 0 (gromovProductAt z y x) := by
      dsimp [s, Ico, Icc] at ht0 ⊢
      push_neg at ht
      have := gromovProductAt_add y z x
      have := gromovProductAt_commute y x z
      constructor <;>
      linarith
    have w2 : w = Gyz.param z s := by
      rw [htw, geodesic_segment_reverse_param hyz ht0]
    have : dist w (Gxz.param z s) ≤ 4 * δ := by
      rw [w2]
      exact thin_triangles1 hyz.symm hxz.symm hs.1 hs.2.le
    refine le_trans ?_ this
    apply infDist_le_dist_of_mem
    apply mem_union_right
    refine hxz.symm.param3 ⟨hs.1, ?_⟩
    calc s ≤ _ := hs.2.le
      _ ≤ _ := (gromovProductAt_le_dist _ _ _).2

/-- The distance of a vertex of a triangle to the opposite side is essentially given by the
Gromov product, up to `2 * δ`. -/
lemma dist_triangle_side_middle {x y : X} {G : Set X} (z : X) (hxy : GeodesicSegmentBetween G x y) :
    dist z (G.param x (gromovProductAt x z y))
      ≤ gromovProductAt z x y + 2 * δ := by
  let m := G.param x (gromovProductAt x z y)
  have : m ∈ G := by
    refine hxy.param3 ⟨?_, ?_⟩
    · exact gromovProductAt_nonneg x z y
    · exact (gromovProductAt_le_dist _ _ _).2
  have A : dist x m = gromovProductAt x z y := by
    refine hxy.param6 ⟨?_, ?_⟩
    · exact gromovProductAt_nonneg x z y
    · exact (gromovProductAt_le_dist _ _ _).2
  have B : dist x m + dist m y = dist x y := hxy.dist_eq this
  have hxzym : dist x z + dist y m = gromovProductAt z x y + dist x y := by
    simp only [dist_comm, gromovProductAt] at A B ⊢
    linarith
  have hxmyz : dist x m + dist y z = gromovProductAt z x y + dist x y := by
    simp only [dist_comm, gromovProductAt] at A B ⊢
    linarith
  have : dist x y + dist z m ≤ max (dist x z + dist y m) (dist x m + dist y z) + 2 * δ :=
    hyperb_quad_ineq ..
  have : dist z m ≤ gromovProductAt z x y + 2 * δ := by
    rw [hxzym, hxmyz, max_self] at this
    linarith
  exact this

-- needed for `dist_along_quasiconvex`
lemma infDist_triangle_side {x y : X} (z : X) {G : Set X} (hxy : GeodesicSegmentBetween G x y) :
    infDist z G ≤ gromovProductAt z x y + 2 * δ := by
  refine le_trans ?_ <| dist_triangle_side_middle z hxy
  apply infDist_le_dist_of_mem
  refine hxy.param3 ⟨?_, ?_⟩
  · exact gromovProductAt_nonneg x z y
  · exact (gromovProductAt_le_dist _ _ _).2

/-- The distance of a point on a side of triangle to the opposite vertex is controlled by
the length of the opposite sides, up to `δ`. -/
-- needed for `Morse_Gromov_theorem_aux2`
lemma dist_le_max_dist_triangle {x y m : X} {G : Set X} (hxy : GeodesicSegmentBetween G x y)
    (hm : m ∈ G) (z : X) :
    dist m z ≤ max (dist x z) (dist y z) + δ := by
  obtain hmx | hmx := le_or_lt (dist m x) δ
  · have : dist m z ≤ dist m x + dist x z := dist_triangle ..
    refine this.trans ?_
    rw [add_comm]
    gcongr
    exact le_max_left ..
  obtain hmy | hmy := le_or_lt (dist m y) δ
  · have : dist m z ≤ dist m y + dist y z := dist_triangle ..
    refine this.trans ?_
    rw [add_comm]
    gcongr
    exact le_max_right ..
  obtain hzxmy | hzxmy := le_or_lt (gromovProductAt z x m) (gromovProductAt z m y)
  · have :=
    calc gromovProductAt z x m = min (gromovProductAt z x m) (gromovProductAt z m y) :=
          min_eq_left hzxmy |>.symm
      _ ≤ gromovProductAt z x y + δ := hyperb_ineq' z x m y
    dsimp [gromovProductAt] at this
    have : dist x m + dist m y = dist x y := hxy.dist_eq hm
    have := le_max_right (dist x z) (dist y z)
    simp only [dist_comm] at *
    linarith
  · have :=
    calc gromovProductAt z y m = min (gromovProductAt z x m) (gromovProductAt z m y) :=
          by simpa [gromovProductAt_commute] using min_eq_right hzxmy.le |>.symm
      _ ≤ gromovProductAt z x y + δ := hyperb_ineq' z x m y
    dsimp [gromovProductAt] at this
    have : dist x m + dist m y = dist x y := hxy.dist_eq hm
    have := le_max_left (dist x z) (dist y z)
    simp only [dist_comm] at *
    linarith

/-- A useful variation around the previous properties is that quadrilaterals are thin, in the
following sense: if one has a union of three geodesics from `x` to `t`, then a geodesic from `x`
to `t` remains within distance `8 * δ` of the union of these 3 geodesics. We formulate the
statement in geodesic hyperbolic spaces as the proof requires the construction of an additional
geodesic, but in fact the statement is true without this assumption, thanks to the Bonk-Schramm
extension theorem. -/
-- needed for `quasiconvex_thickening`
lemma thin_quadrilaterals [GeodesicSpace X] {x y z t w : X}
    {Gxy : Set X} (hxy : GeodesicSegmentBetween Gxy x y)
    {Gyz : Set X} (hyz : GeodesicSegmentBetween Gyz y z)
    {Gzt : Set X} (hzt : GeodesicSegmentBetween Gzt z t)
    {Gxt : Set X} (hxt : GeodesicSegmentBetween Gxt x t)
    (hw : w ∈ Gxt) :
    infDist w (Gxy ∪ Gyz ∪ Gzt) ≤ 8 * δ := by
  have I : infDist w ({x‒z} ∪ Gzt) ≤ 4 * δ := thin_triangles [x‒z].symm hzt hxt hw
  obtain ⟨u, hu_mem, hu_dist⟩ : ∃ u ∈ {x‒z} ∪ Gzt, infDist w ({x‒z} ∪ Gzt) = dist w u := by
    apply ([x‒z].isCompact.union hzt.isCompact).exists_infDist_eq_dist
    use x
    left
    exact [x‒z].left_mem
  have : infDist u (Gxy ∪ Gyz ∪ Gzt) ≤ 4 * δ := by
    by_cases h : u ∈ {x‒z}
    · calc infDist u (Gxy ∪ Gyz ∪ Gzt) ≤ infDist u (Gxy ∪ Gyz) := by
            rw [union_assoc]
            gcongr
            · refine ⟨y, ?_⟩
              left
              exact hxy.right_mem
            · aesop
        _ ≤ 4 * δ := thin_triangles hxy.symm hyz [x‒z] h
    · have : u ∈ Gzt := by aesop
      calc infDist u (Gxy ∪ Gyz ∪ Gzt) ≤ infDist u Gzt := by
            gcongr
            · exact ⟨_, this⟩
            · aesop
        _ = 0 := infDist_zero_of_mem this
        _ ≤ 4 * δ := by
            have : Inhabited X := ⟨u⟩
            have := delta_nonneg X
            positivity
  have : infDist w (Gxy ∪ Gyz ∪ Gzt) ≤ infDist u (Gxy ∪ Gyz ∪ Gzt) + dist w u :=
    infDist_le_infDist_add_dist
  linarith
