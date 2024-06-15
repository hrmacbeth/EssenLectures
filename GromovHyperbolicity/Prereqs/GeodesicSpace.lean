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
def GeodesicSegmentBetween (G : Set X) (x y : X) : Prop :=
  ∃ g : ℝ → X, g 0 = x ∧ g (dist x y) = y ∧ Isometry (g ∘ Subtype.val : Icc 0 (dist x y) → _)
    ∧ G = g '' Icc 0 (dist x y)

def GeodesicSegment (G : Set X) : Prop := ∃ x y, GeodesicSegmentBetween G x y

/-! We also introduce the parametrization of a geodesic segment. It is convenient to use the
following definition, which guarantees that the point is on `G` even without checking that `G`
is a geodesic segment or that the parameter is in the reasonable range: this shortens some
arguments below. -/
noncomputable def Set.param (G : Set X) (x : X) (t : ℝ) : X :=
  if h : ∃ w ∈ G, dist x w = t then
    h.choose
  else if h : G.Nonempty then
    h.choose
  else
    have : Nonempty X := ⟨x⟩
    Classical.ofNonempty

lemma GeodesicSegmentBetween.left_mem {G : Set X} {x y : X}
    (hxy : GeodesicSegmentBetween G x y) : x ∈ G := by
  sorry

lemma GeodesicSegmentBetween.right_mem {G : Set X} {x y : X}
    (hxy : GeodesicSegmentBetween G x y) : y ∈ G := by
  sorry

/- Just like an interval, a geodesic segment is nonempty. -/
lemma GeodesicSegmentBetween.nonempty {G : Set X} {x y : X} (h : GeodesicSegmentBetween G x y) :
    G.Nonempty := by
  sorry

lemma GeodesicSegmentBetween.symm {G : Set X} {x y : X} (hG : GeodesicSegmentBetween G x y) :
    GeodesicSegmentBetween G y x := sorry

lemma GeodesicSegmentBetween.dist_eq {G : Set X} {x y : X} (hGxy : GeodesicSegmentBetween G x y)
    {a : X} (haG : a ∈ G) :
    dist x a + dist a y = dist x y := by
  sorry

lemma GeodesicSegmentBetween.dist_le {G : Set X} {x y : X} (hGxy : GeodesicSegmentBetween G x y)
    {a : X} (haG : a ∈ G) :
    dist x a ≤ dist x y := by
  have : 0 ≤ dist a y := dist_nonneg
  have := hGxy.dist_eq haG
  linarith

lemma GeodesicSegmentBetween.param1 {G : Set X} {x y : X} (h : GeodesicSegmentBetween G x y) :
    G.param x 0 = x := by
  sorry

lemma GeodesicSegmentBetween.param2 {G : Set X} {x y : X} (h : GeodesicSegmentBetween G x y) :
    G.param x (dist x y) = y := by
  sorry

lemma GeodesicSegmentBetween.param3 {G : Set X} {x y : X} (h : GeodesicSegmentBetween G x y) {t : ℝ}
    (h' : t ∈ Icc 0 (dist x y)) :
    G.param x t ∈ G := by
  sorry

lemma GeodesicSegmentBetween.param4 {G : Set X} {x y : X} (h : GeodesicSegmentBetween G x y) :
    Isometry (G.param x ∘ Subtype.val : Icc (0:ℝ) (dist x y) → _) := by
  sorry

lemma GeodesicSegmentBetween.param5 {G : Set X} {x y : X} (h : GeodesicSegmentBetween G x y) :
    (G.param x) '' (Icc 0 (dist x y)) = G := by
  sorry

lemma GeodesicSegmentBetween.param6 {G : Set X} {x y : X} (h : GeodesicSegmentBetween G x y) {t : ℝ}
    (h1 : t ∈ Icc 0 (dist x y)) :
    dist x (G.param x t) = t := by
  sorry

lemma GeodesicSegmentBetween.param7 {G : Set X} {x y : X} (h : GeodesicSegmentBetween G x y) {s t : ℝ}
    (h1 : s ∈ Icc 0 (dist x y)) (h2 : t ∈ Icc 0 (dist x y)) :
    dist (G.param x s) (G.param x t) = |s - t| := by
  sorry

lemma GeodesicSegmentBetween.param8 {G : Set X} {x y : X} (h : GeodesicSegmentBetween G x y) {z : X}
    (h1 : z ∈ G) :
    z = G.param x (dist x z) := by
  sorry

lemma geodesic_segment_param_in_segment {G : Set X} (hG : G.Nonempty) {x : X} {t : ℝ} :
    G.param x t ∈ G :=
  sorry

lemma GeodesicSegmentBetween.param_in_segment {G : Set X} {x y : X}
    (h : GeodesicSegmentBetween G x y) {t : ℝ} :
    G.param x t ∈ G :=
  geodesic_segment_param_in_segment h.nonempty

lemma geodesic_segment_reverse_param {G : Set X} {x y : X}
    (hxy : GeodesicSegmentBetween G x y) {t : ℝ} (ht : t ∈ Icc 0 (dist x y)) :
    G.param y (dist x y - t) = G.param x t := by
  sorry

lemma GeodesicSegmentBetween.dist_along_wrt_endpoint {G : Set X} {x y : X}
    (hxy : GeodesicSegmentBetween G x y) {u : X} (hu : u ∈ G) {v : X} (hv : v ∈ G) :
    dist u v = |dist u x - dist v x| := by
  sorry

/-- One often needs to restrict a geodesic segment to a subsegment. We introduce the tools
to express this conveniently. -/
def geodesic_subsegment (G : Set X) (x : X) (s t : ℝ) : Set X :=
  G ∩ {z | dist x z ≥ s ∧ dist x z ≤ t}

/--  A subsegment is indeed a geodesic segment, and its endpoints and parametrization can be
expressed in terms of the original segment. -/
lemma geodesic_subsegment1 {G : Set X} {x y : X} (hG : GeodesicSegmentBetween G x y) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ dist x y) :
    geodesic_subsegment G x s t = (G.param x) '' (Icc s t) :=
  sorry

lemma geodesic_subsegment2 {G : Set X} {x y : X} (hG : GeodesicSegmentBetween G x y) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ dist x y) :
    GeodesicSegmentBetween (geodesic_subsegment G x s t) (G.param x s) (G.param x t) :=
  sorry

lemma geodesic_subsegment3 {G : Set X} {x y : X} (hG : GeodesicSegmentBetween G x y) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ dist x y) {u : ℝ} (hsu : s ≤ u) (hut : u ≤ t) :
    (geodesic_subsegment G x s t).param (G.param x s) (u - s) = G.param x u := by
  sorry

/-- A segment contains a subsegment between any of its points. -/
lemma geodesic_subsegment_exists {G : Set X} (hG : GeodesicSegment G) {x y : X} (hx : x ∈ G) (hy : y ∈ G) :
    ∃ H : Set X, H ⊆ G ∧ GeodesicSegmentBetween H x y := by
  sorry

/- Just like an interval, a geodesic segment is compact. -/
lemma GeodesicSegmentBetween.isCompact {G : Set X} {x y : X} (h : GeodesicSegmentBetween G x y) :
    IsCompact G := by
  sorry

/- Just like an interval, a geodesic segment is connected. -/
lemma GeodesicSegmentBetween.isConnected {G : Set X} {x y : X} (h : GeodesicSegmentBetween G x y) :
    IsConnected G := by
  sorry

/- Just like an interval, a geodesic segment is path-connected. -/
lemma GeodesicSegmentBetween.isPathConnected {G : Set X} {x y : X} (h : GeodesicSegmentBetween G x y) :
    IsPathConnected G := by
  sorry

/- Just like an interval, a geodesic segment is bounded. -/
lemma GeodesicSegmentBetween.isBounded {G : Set X} {x y : X} (h : GeodesicSegmentBetween G x y) :
    Bornology.IsBounded G := by
  sorry

/- Just like an interval, a geodesic segment is closed. -/
lemma GeodesicSegmentBetween.isClosed {G : Set X} {x y : X} (h : GeodesicSegmentBetween G x y) :
    IsClosed G := by
  sorry

/-- If a point `y` is on a geodesic segment between `x` and its closest projection `p` on a set `A`,
then `p` is also a closest projection of `y`, and the closest projection set of `y` is contained in
that of `x`. -/
lemma GeodesicSegmentBetween.projSet_same_basepoint {x y p : X} {A : Set X} (hp : p ∈ projSet x A) {G : Set X}
    (hG : GeodesicSegmentBetween G p x) (hy : y ∈ G) :
    p ∈ projSet y A := by
  sorry

lemma GeodesicSegmentBetween.projSet_thickening {p x : X} {Z : Set X} (hp : p ∈ projSet x Z) {D : ℝ} (hD : 0 ≤ D)
    (hD' : D ≤ dist p x) {G : Set X} (hG : GeodesicSegmentBetween G p x) :
    G.param p D ∈ projSet (G.param p D) (Metric.cthickening D Z) := by
  sorry

lemma GeodesicSegmentBetween.projSet_thickening' {p x : X} {Z : Set X} (hp : p ∈ projSet x Z) {D : ℝ} (hD : 0 ≤ D)
    {E : ℝ} (hDE : D ≤ E) (hE : E ≤ dist p x) {G : Set X} (hG : GeodesicSegmentBetween G p x) :
    G.param p D ∈ projSet (G.param p E) (Metric.cthickening D Z) := by
  sorry

/-- It is often convenient to use *one* geodesic between `x` and `y`, even if it is not unique.
We introduce a notation for such a choice of a geodesic, denoted `{x‒y}` for such a geodesic.
We also enforce the condition `{x‒y} = {y‒x}`.
When there is no such geodesic, we simply take `{x‒y} = {x,y}` for definiteness.
It would be even better to enforce that, if
`a` is on `{x‒y}`, then `{x‒y}` is the union of `{x‒a}` and `{a‒y}`, but
I do not know if such a choice is always possible -- such a choice of geodesics is
called a geodesic bicombing.

We prove that there is such a choice of geodesics, compatible with direction reversal. What
we do is choose arbitrarily a geodesic between `x` and `y` if it exists, and then use the geodesic
between `min x y` and `max x y`, for any total order on the space, to ensure that we get the
same result from `x` to `y` or from `y` to `x`. -/
lemma some_geodesicSegmentBetween_exists (X : Type*) [MetricSpace X]
    [∀ x y : X, Decidable (∃ G, GeodesicSegmentBetween G x y)] :
    ∃ f : X → X → Set X, ∀ x y, f x y = f y x
    ∧  (if (∃ G, GeodesicSegmentBetween G x y) then
          (GeodesicSegmentBetween (f x y) x y)
        else
          f x y = {x, y}) :=
  sorry

/-- It is often convenient to use \emph{one} geodesic between `x` and `y`, even if it is not unique.
We introduce a notation for such a choice of a geodesic, denoted `{x‒S‒y}` for such a geodesic
that moreover remains in the set `S`. We also enforce
the condition `{x‒S‒y} = {y‒S‒x}`. When there is no such geodesic, we simply take
`{x‒S‒y} = {x, y}` for definiteness. It would be even better to enforce that, if
`a` is on `{x‒S‒y}`, then `{x‒S‒y}` is the union of `{x‒S‒a}` and `{a‒S‒y}` but
I do not know if such a choice is always possible -- such a choice of geodesics is
called a geodesic bicombing. -/
def some_geodesicSegmentBetween_UNIV {X : Type*} [MetricSpace X]
    [∀ x y : X, Decidable (∃ G, GeodesicSegmentBetween G x y)]
    (x y : X) : Set X :=
  (some_geodesicSegmentBetween_exists X).choose x y

set_option quotPrecheck false in
notation "{" x "‒" y "}" => some_geodesicSegmentBetween_UNIV x y

/-! ## Geodesic spaces

In this subsection, we define geodesic spaces (metric spaces in which there is a geodesic
segment joining any pair of points). -/

class GeodesicSpace (X : Type*) [MetricSpace X] :=
  (exists_geodesic : ∀ x y : X, ∃ G, GeodesicSegmentBetween G x y)

variable [GeodesicSpace X]

@[simp] lemma some_geodesic_is_geodesic_segment1 (x y : X) :
    GeodesicSegmentBetween {x‒y} x y := by
  sorry

set_option quotPrecheck false in
notation "[" x "‒" y "]" => some_geodesic_is_geodesic_segment1 x y
