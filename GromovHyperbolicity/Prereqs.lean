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

-- note: made up this name, it was recorded as geodesic_segment_param(6)
theorem dist_geodesic_segment_param {X : Type*} [MetricSpace X] (G : Set X) (x : X) (t : ℝ) :
    dist x (geodesic_segment_param G x t) ≤ t :=
  sorry

class GeodesicSpace (X : Type*) [MetricSpace X]

-- **Lemma 2.1**
-- `quasi_geodesic_made_lipschitz`

-- `infDist_almost_attained`
-- `infDist_proper_attained`
-- `proj_set_dist_le`
-- `geodesic_segment_topology`
-- `geodesic_subsegment_exists`

open Set Topology in
-- there must be a better way! check the library
theorem method_of_continuity {a b : ℝ} (hab : a ≤ b) {P : ℝ → Prop} (hPa : P a) :
    ∃ u ∈ Icc a b, (∀ s ∈ Ico a u, P s) ∧ (u < b → ∃ᶠ s in 𝓝[≥] u, ¬ P s) := by
  let I : Set ℝ := Icc a b ∩ {t | ∀ s ∈ Icc a t, P s}
  have haI : a ∈ I := by
    refine ⟨by aesop, ?_⟩
    intro s hs
    obtain rfl : s = a := by simpa using hs
    aesop
  have : BddAbove I := BddAbove.inter_of_left bddAbove_Icc
  let u := sSup I
  have hau : a ≤ u := le_csSup this haI
  have A : ∀ s ∈ Ico a u, P s := by
    intro s hs
    obtain ⟨t, htI, hts⟩ : ∃ t ∈ I, s < t := exists_lt_of_lt_csSup ⟨_, haI⟩ hs.2
    exact htI.2 _ ⟨hs.1, hts.le⟩
  refine ⟨u, ⟨hau, csSup_le ⟨_, haI⟩ <| by aesop⟩, A, ?_⟩
  intro hub
  rw [Filter.frequently_iff]
  intro s hs
  rw [mem_nhdsWithin_Ici_iff_exists_Icc_subset] at hs
  obtain ⟨e, he, heus⟩ := hs
  have hu_lt : u < min b e := lt_min hub he
  have hmin_mem : min b e ∈ Icc a b := ⟨hau.trans hu_lt.le, min_le_left _ _⟩
  have h := not_mem_of_csSup_lt hu_lt (by assumption)
  change ¬ (_ ∧ ∀ _, _) at h
  push_neg at h
  obtain ⟨x, hx1, hx2⟩ := h hmin_mem
  refine ⟨x, heus ⟨?_, hx1.2.trans (min_le_right ..)⟩, hx2⟩
  by_contra! hxu
  have := A x ⟨hx1.1, hxu⟩
  exact hx2 this
