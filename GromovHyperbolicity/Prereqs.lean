/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD -/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UniformSpace.Completion

/-! # TODO Missing geodesic space theory -/

open Metric

open UniformSpace in
@[elab_as_elim]
theorem UniformSpace.Completion.induction_on₄ [UniformSpace α] [UniformSpace β] [UniformSpace γ] [UniformSpace δ]
    {p : Completion α → Completion β → Completion γ → Completion δ → Prop}
    (a : Completion α) (b : Completion β) (c : Completion γ) (d : Completion δ)
    (hp : IsClosed { x : Completion α × Completion β × Completion γ × Completion δ | p x.1 x.2.1 x.2.2.1 x.2.2.2 })
    (ih : ∀ (a : α) (b : β) (c : γ) (d : δ), p a b c d) : p a b c d :=
  sorry

def quasi_isometry_on (lambda C : ℝ) {X Y : Type*} [MetricSpace X] [MetricSpace Y] (s : Set X) (f : X → Y) : Prop := sorry

def proj_set {X : Type*} [MetricSpace X] (x : X) (s : Set X) : Set X := sorry

lemma proj_setD [MetricSpace X] {x y : X} {s : Set X} (hxy : x ∈ proj_set y s) : x ∈ s := sorry

def geodesic_segment {X : Type*} [MetricSpace X] (s : Set X) : Prop := sorry

def geodesic_segment_between {X : Type*} [MetricSpace X] (s : Set X) (x y : X) : Prop := sorry

lemma some_geodesic_segment_between_exists (X : Type*) [MetricSpace X]
    [∀ x y : X, ∀ S : Set X, Decidable (∃ G, geodesic_segment_between G x y ∧ G ⊆ S)] :
    ∃ f : X → Set X → X → Set X, ∀ x y S, f x S y = f y S x
    ∧  (if (∃ G, geodesic_segment_between G x y ∧ G ⊆ S) then
          (geodesic_segment_between (f x S y) x y ∧ (f x S y ⊆ S))
        else
          f x S y = {x, y}) :=
  sorry

def some_geodesic_segment_between {X : Type*} [MetricSpace X]
    [∀ x y : X, ∀ S : Set X, Decidable (∃ G, geodesic_segment_between G x y ∧ G ⊆ S)]
    (x y : X) (S : Set X) : Set X :=
  (some_geodesic_segment_between_exists X).choose x S y

set_option quotPrecheck false in
notation "{" x "‒" S "‒" y "}" => some_geodesic_segment_between x y S

abbrev some_geodesic_segment_between_UNIV {X : Type*} [MetricSpace X]
    [∀ x y : X, ∀ S : Set X, Decidable (∃ G, geodesic_segment_between G x y ∧ G ⊆ S)]
    (x y : X) : Set X :=
  {x‒(@Set.univ X)‒y}

set_option quotPrecheck false in
notation "{" x "‒" y "}" => some_geodesic_segment_between_UNIV x y

def geodesic_segment_param {X : Type*} [MetricSpace X] (G : Set X) (x : X) (t : ℝ) : X := sorry

class GeodesicSpace (X : Type*) [MetricSpace X]

-- **Lemma 2.1**
-- `quasi_geodesic_made_lipschitz`

-- `infDist_almost_attained`
-- `infDist_proper_attained`
-- `proj_set_dist_le`
-- `geodesic_segment_topology`
