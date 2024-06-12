/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD -/
import Examples.Day1
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Set Metric Real Classical

/-! ## Closest point projection -/

section
variable {X : Type*} [MetricSpace X]

def proj_set (x : X) (A : Set X) : Set X := {y | y ∈ A ∧ dist x y = infDist x A}

lemma proj_set_dist_le {x y p : X} {A : Set X} (hy : y ∈ A) (hpx : p ∈ proj_set x A) :
    dist x p ≤ dist x y :=
  hpx.2 ▸ infDist_le_dist_of_mem hy

end

section
variable {X : Type*} [MetricSpace X] [GromovHyperbolicSpace X]

-- some missing definitions (we'll come back to these later)
structure GeodesicSegmentBetween (x y : X) :=
  (set : Set X)

def GeodesicSegmentBetween.param {x y : X} (G : GeodesicSegmentBetween x y) : ℝ → X := sorry

class GeodesicSpace (X : Type*) [MetricSpace X] : Prop :=
  (exists_geodesic : ∀ x y : X, Nonempty (GeodesicSegmentBetween x y))

set_option quotPrecheck false
notation "{" x "‒" y "}" => Classical.choice (GeodesicSpace.exists_geodesic x y)

end

/-! ## Exponential contraction of the projection -/


/-! The main result of this file is `quasiconvex_projection_exp_contracting`, a key technical result
used in the Gouëzel-Shchur quantitative Morse lemma. -/

variable {X : Type*} [MetricSpace X] [GromovHyperbolicSpace X] [GeodesicSpace X]

open GromovHyperbolicSpace BigOperators

variable {G : Set X} {x y : X}

/-- The next lemma (for `C = 0`, Lemma 2 in~\<^cite> "shchur") asserts that, if two points are not too far apart (at distance at most
`10 * δ`), and far enough from a given geodesic segment, then when one moves towards this
geodesic segment by a fixed amount (here `5 * δ`), then the two points become closer (the new
distance is at most `5 * δ`, gaining a factor of `2`). Later, we will iterate this lemma to
show that the projection on a geodesic segment is exponentially contracting. For the application,
we give a more general version involving an additional constant `C`.

This lemma holds for `δ` the hyperbolicity constant. We will want to apply it with `δ > 0`,
so to avoid problems in the case `δ = 0` we formulate it not using the hyperbolicity constant of
the given type, but any constant which is at least the hyperbolicity constant (this is to work
around the fact that one can not say or use easily in Isabelle that a type with hyperbolicity
`δ` is also hyperbolic for any larger constant `δ'`. -/
lemma geodesic_projection_exp_contracting_aux {a b : X} (G : GeodesicSegmentBetween a b) {x y px py : X}
    (hpxG : px ∈ proj_set x G.set) (hpyG : py ∈ proj_set y G.set) {δ C : ℝ}
    (hδ : δ ≥ deltaG X) {M : ℝ} (hxy : dist x y ≤ 10 * δ + C)
    (hM : M ≥ 15/2 * δ) (hpx : M + 5 * δ + C/2 ≤ dist px x) (hpy : M + 5 * δ + C/2 ≤ dist py y)
    (hC : C ≥ 0) :
    dist ({px‒x}.param M) ({py‒y}.param M) ≤ 5 * δ := by
  have hpxpyx : dist px x ≤ dist py x := by
    simpa only [dist_comm] using proj_set_dist_le hpyG.1 hpxG
  have hpypxy : dist py y ≤ dist px y := by
    simpa only [dist_comm] using proj_set_dist_le hpxG.1 hpyG
  have hδ₀ : 0 ≤ δ := sorry
  have hM' : 0 ≤ M ∧ M ≤ dist px x ∧ M ≤ dist px y ∧ M ≤ dist py x ∧ M ≤ dist py y := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have : px ∈ G.set ∧ py ∈ G.set := ⟨hpxG.1, hpyG.1⟩
  set x' := {px‒x}.param M
  set y' := {py‒y}.param M
  /- First step: the distance between `px` and `py` is at most `5 * δ`. -/
  have hpxpyδ :=
  calc dist px py
      ≤ max (5 * deltaG X) (dist x y - dist px x - dist py y + 10 * deltaG X) := sorry
    _ ≤ max (5 * deltaG X) (5 * deltaG X) := by
        gcongr
        linarith only [hδ, hxy, hpx, hpy, hM, hδ₀]
    _ ≤ 5 * δ := by
        rw [max_self]
        gcongr
  /- Second step: show that all the interesting Gromov products at bounded below by `M`. -/
  have hx'_mem : x' ∈ {px‒x}.set := sorry
  have : px ∈ proj_set x' G.set := sorry
  have hpxx'M : dist px x' = M := sorry
  have hpxpyx' : dist px x' ≤ dist py x' := by
    simpa only [dist_comm] using proj_set_dist_le hpyG.1 this
  have : dist px x = dist px x' + dist x' x := sorry
  have Ixx : gromovProductAt px x' x = M := by
    dsimp only [gromovProductAt]
    linarith only [this, hpxx'M]
  have Iyx : gromovProductAt py x x' ≥ M := by
    simp only [gromovProductAt, dist_comm] at Ixx hpxpyx hpxpyx' ⊢
    linarith only [Ixx, hpxpyx, hpxpyx']
  have hy'_mem : y' ∈ {py‒y}.set := sorry
  have : py ∈ proj_set y' G.set := sorry
  have hpyy'M : dist py y' = M := sorry
  have hpypyy' : dist py y' ≤ dist px y' := by
    simpa only [dist_comm] using proj_set_dist_le hpxG.1 this
  have : dist py y = dist py y' + dist y' y := sorry
  have Iyy : gromovProductAt py y' y = M := by
    dsimp only [gromovProductAt]
    linarith only [this, hpyy'M]
  have Ixy : gromovProductAt px y y' ≥ M := by
    simp only [gromovProductAt, dist_comm] at Iyy hpypxy hpypyy' ⊢
    linarith only [Iyy, hpypxy, hpypyy']
  have Ix : gromovProductAt px x y ≥ M := by
    dsimp only [gromovProductAt]
    linarith only [hpypxy, hxy, hpx, hpy]
  have Iy : gromovProductAt py x y ≥ M := by
    dsimp only [gromovProductAt] at *
    linarith only [hpxpyx, hxy, hpx, hpy]
  /- Third step: prove the estimate -/
  have A : M - 4 * δ + dist x' y' ≤ dist px y' := by
    have h₁ := le_min Ixx.ge <| le_min Ix Ixy
    have h₂ := hyperb_ineq_4_points px x' x y y'
    change _ ≤ _ / 2 at h₂
    linarith only [hpxx'M, hδ, h₁, h₂]
  have B : M - 4 * δ + dist x' y' ≤ dist py x' := by
    rw [gromovProductAt_commute] at Iyx Iyy
    have h₁ := le_min Iyx.le <| le_min Iy Iyy.ge
    have h₂ := hyperb_ineq_4_points py x' x y y'
    change _ ≤ _ / 2 at h₂
    linarith only [hpyy'M, hδ, h₁, h₂]
  have hpxpy : dist px py ≤ 2 * M - 10 * δ := by linarith only [hpxpyδ, hM]
  have : 2 * M - 10 * δ + 2 * dist x' y'
      ≤ max (dist px py + dist y' x') (dist px x' + dist y' py) := by
    have := hyperb_quad_ineq px y' py x'
    linarith only [this, hδ, A, B]
  have : 2 * M - 10 * δ + 2 * dist x' y' ≤ dist px x' + dist py y' := by
    simp only [dist_comm] at this hpxpy hpxx'M hpyy'M
    rw [le_max_iff] at this
    obtain h | h := this <;> linarith only [this, hpxpy, h, hδ₀, hpxx'M, hpyy'M]
  linarith only [hpxx'M, hpyy'M, this]
