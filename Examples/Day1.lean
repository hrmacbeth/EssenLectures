/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD -/
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Gromov-hyperbolic spaces

This is a first file on Gromov-hyperbolic spaces.  You should play around with it and try to
understand each proof.

-/

open Metric Set Classical

noncomputable section

variable {X : Type*} [MetricSpace X]


/-! ## The Gromov product -/

/-- A good formulation of hyperbolicity will be in terms of Gromov products. Intuitively, the
Gromov product of `x` and `y` based at `e` is the distance between `e` and the geodesic between
`x` and `y`. It is also the time after which the geodesics from `e` to `x` and from `e` to `y`
stop travelling together. -/
def gromovProductAt (e x y : X) : ℝ := (dist e x + dist e y - dist x y) / 2

@[simp] lemma gromovProductAt_nonneg (e x y : X) : gromovProductAt e x y ≥ 0 := by
  have := dist_triangle x e y
  simp only [gromovProductAt, dist_comm] at this ⊢
  linarith

lemma gromovProductAt_commute (e x y : X) : gromovProductAt e x y = gromovProductAt e y x := by
  simp only [gromovProductAt, dist_comm, add_comm]

@[simp] lemma gromovProductAt_le_dist (e x y : X) :
    gromovProductAt e x y ≤ dist e x ∧ gromovProductAt e x y ≤ dist e y := by
  have := dist_triangle e x y
  have := dist_triangle e y x
  simp only [gromovProductAt, dist_comm] at *
  constructor <;> linarith

lemma gromovProductAt_add (e x y : X) :
    gromovProductAt e x y + gromovProductAt x e y = dist e x := by
  simp only [gromovProductAt, dist_comm]
  ring

@[simp] lemma gromovProductAt_e_x_x (e x : X) : gromovProductAt e x x = dist e x := by
  simp [gromovProductAt]

/-- The Gromov product is continuous in its three variables. -/
@[fun_prop] lemma gromovProductAt_continuous :
    Continuous (fun (p : X × X × X) ↦ gromovProductAt p.1 p.2.1 p.2.2) := by
  simp only [gromovProductAt]
  fun_prop (disch := norm_num)

end

/-! ## Definition, basic properties -/

/-- A set is δ-hyperbolic if it satisfies the following inequality. It is very obscure at first
sight, but we will see several equivalent characterizations later on. For instance, a space is
hyperbolic (maybe for a different constant δ) if all geodesic triangles are thin, i.e., every side
is close to the union of the two other sides. This definition captures the main features of negative
curvature at a large scale, and has proved extremely fruitful and influential. -/
class GromovHyperbolicSpace (X : Type*) [MetricSpace X] where
  deltaG : ℝ
  delta_nonneg : 0 ≤ deltaG
  hyperb_quad_ineq0 : ∀ x y z t : X,
    dist x y + dist z t ≤ max (dist x z + dist y t) (dist x t + dist y z) + 2 * deltaG

variable {X : Type*} [MetricSpace X] [GromovHyperbolicSpace X]

local notation "δ" => GromovHyperbolicSpace.deltaG X

lemma GromovHyperbolicSpace.hyperb_quad_ineq (x y z t : X) :
    dist x y + dist z t ≤ max (dist x z + dist y t) (dist x t + dist y z) + 2 * δ :=
  GromovHyperbolicSpace.hyperb_quad_ineq0 x y z t

open GromovHyperbolicSpace

lemma hyperb_ineq (e x y z : X) :
    gromovProductAt e x z ≥ min (gromovProductAt e x y) (gromovProductAt e y z) - δ := by
  replace H : dist e y + dist x z - 2 * δ ≤ max (dist e x + dist y z) (dist e z + dist y x):= by
    linarith [hyperb_quad_ineq e y x z]
  rw [le_max_iff] at H
  suffices
    min (gromovProductAt e x y) (gromovProductAt e y z) ≤ gromovProductAt e x z + δ by linarith
  rw [min_le_iff]
  simp only [gromovProductAt, dist_comm] at *
  by_contra! H'
  obtain H₁ | H₂ := H
  · linarith
  · linarith

lemma hyperb_ineq' (e x y z : X) :
    gromovProductAt e x z + δ ≥ min (gromovProductAt e x y) (gromovProductAt e y z) := by
  have := hyperb_ineq e x y z
  linarith only [this]

lemma hyperb_ineq_4_points (e x y z t : X) :
    min (gromovProductAt e x y) (min (gromovProductAt e y z) (gromovProductAt e z t)) - 2 * δ
    ≤ gromovProductAt e x t := by
  have h1 : min (gromovProductAt e x y) (gromovProductAt e y z) ≤ gromovProductAt e x z + δ := by
    linarith [hyperb_ineq e x y z]
  have h2 : min (gromovProductAt e x z) (gromovProductAt e z t) ≤ gromovProductAt e x t + δ := by
    linarith [hyperb_ineq e x z t]
  suffices min (gromovProductAt e x y) (min (gromovProductAt e y z) (gromovProductAt e z t))
      ≤ gromovProductAt e x t + 2 * δ by linarith
  rw [min_le_iff] at h1
  rw [min_le_iff] at h2
  rw [min_le_iff, min_le_iff]
  have : 0 ≤ δ := delta_nonneg
  by_contra!
  obtain h1a | h1b := h1 <;> obtain h2a | h2b := h2 <;> linarith

lemma hyperb_ineq_4_points' (e x y z t : X) :
    min (gromovProductAt e x y) (min (gromovProductAt e y z) (gromovProductAt e z t))
    ≤ gromovProductAt e x t + 2 * δ := by
  have := hyperb_ineq_4_points e x y z t
  aesop
