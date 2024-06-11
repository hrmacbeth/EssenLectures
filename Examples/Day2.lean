/-  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD -/
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Examples.Day1

open Set Metric Real Classical GromovHyperbolicSpace

/-! ## Chains of calculations -/

example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 :=
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by gcongr
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by gcongr
    _ > 3 := by norm_num

-- Exercise: replace the words "sorry" with the correct Lean justification.
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 :=
  calc
    r = (s + r + r - s) / 2 := by sorry
    _ ≤ (3 + (s + 3) - s) / 2 := by sorry
    _ = 3 := by sorry

example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : x + y < 2 :=
  sorry

-- Exercise: replace the words "sorry" with the correct Lean justification.
example {u v x y A B : ℝ} (h1 : 0 < A) (h2 : A ≤ 1) (h3 : 1 ≤ B) (h4 : x ≤ B)
    (h5 : y ≤ B) (h6 : 0 ≤ u) (h7 : 0 ≤ v) (h8 : u < A) (h9 : v < A) :
    u * y + v * x + u * v < 3 * A * B :=
  calc
    u * y + v * x + u * v
      ≤ u * B + v * B + u * v := by sorry
    _ ≤ A * B + A * B + A * v := by sorry
    _ ≤ A * B + A * B + 1 * v := by sorry
    _ ≤ A * B + A * B + B * v := by sorry
    _ < A * B + A * B + B * A := by sorry
    _ = 3 * A * B := by sorry

-- Exercise: replace the words "sorry" with the correct Lean justification.
example {t : ℚ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 :=
  calc
    t ^ 2 - 3 * t - 17
      = t * t - 3 * t - 17 := by sorry
    _ ≥ 10 * t - 3 * t - 17 := by sorry
    _ = 7 * t - 17 := by sorry
    _ ≥ 7 * 10 - 17 := by sorry
    _ ≥ 5 := by sorry

example {x y : ℝ} (h : x ^ 2 + y ^ 2 ≤ 1) : (x + y) ^ 2 < 3 :=
  calc
    (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by
        have : 0 ≤ (x - y) ^ 2 := by positivity
        linarith
    _ = 2 * (x ^ 2 + y ^ 2) := by sorry
    _ ≤ 2 * 1 := by sorry
    _ < 3 := by sorry


example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  sorry

example {x : ℚ} : x ^ 2 - 2 * x ≥ -1 :=
  sorry

example (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b :=
  sorry

/-! ## Quasi-isometries

The "quasi-isometry" definition includes quasi-geodesics as a special case (by taking `X` to be
`ℝ`). -/

section QuasiIsometry

variable {X : Type*} [MetricSpace X] {Y : Type*} [MetricSpace Y]

/-- A `(Λ, C)` quasi-isometry is a function which behaves like an isometry, up to
an additive error `C` and a multiplicative error `Λ`. It can be very different from an
isometry on small scales (for instance, the function integer part is a quasi-isometry between
`ℝ` and `ℤ`), but on large scales it captures many important features of
isometries.

When the space is unbounded, one checks easily that `C ≥ 0` and `Λ ≥ 1`. As this
is the only case of interest (any two bounded sets are quasi-isometric), we incorporate
this requirement in the definition. -/
structure QuasiIsometryOn (Λ C : ℝ) (s : Set X) (f : X → Y) : Prop :=
  (one_le_Λ : 1 ≤ Λ)
  (C_nonneg : 0 ≤ C)
  (upper_bound {x y : X} (_ : x ∈ s) (_ : y ∈ s) : dist (f x) (f y) ≤ Λ * dist x y + C)
  (lower_bound {x y : X} (_ : x ∈ s) (_ : y ∈ s) : Λ⁻¹ * dist x y - C ≤ dist (f x) (f y))

-- Exercise: fill in these four proofs
theorem QuasiIsometryOn.mono {Λ Λ' C C': ℝ} {s : Set X} {f : X → Y} (hΛ : Λ ≤ Λ') (hC : C ≤ C')
    (hf : QuasiIsometryOn Λ C s f) :
    QuasiIsometryOn Λ' C' s f where
  one_le_Λ := sorry
  C_nonneg := sorry
  upper_bound := sorry
  lower_bound := sorry

end QuasiIsometry

-- some missing definitions (we'll come back to these later)
def GeodesicSegmentBetween (G : Set X) (x y : X) : Prop := sorry
class GeodesicSpace (X : Type*) [MetricSpace X] : Prop


/-! ## A step in the final reduction of the theorem -/

variable {X : Type*} [MetricSpace X] [GeodesicSpace X] [GromovHyperbolicSpace X]

local notation "δ" => GromovHyperbolicSpace.deltaG X

/-- The main induction is over. To conclude, one should apply its result to the original
geodesic segment joining the points `f(a)` and `f(b)`. -/
lemma Morse_Gromov_theorem_aux1
    {f : ℝ → X} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    {Λ C : ℝ} (hf' : QuasiIsometryOn Λ C (Icc a b) f)
    (hab : a ≤ b)
    {G : Set X} (hGf : GeodesicSegmentBetween G (f a) (f b))
    {z : ℝ} (hz : z ∈ Icc a b) :
    infDist (f z) G ≤ Λ ^ 2 * (11/2 * C + 95 * δ) := by
  have := hf'.C_nonneg
  have := hf'.one_le_Λ
  have : 0 < δ := sorry -- for simplicity, separate argument if `δ = 0`

  /- We give their values to the parameters `L`, `D` and `α` that we will use in the proof.
  We also define two constants `K₁` and `K₂` that appear in the precise formulation of the
  bounds. Their values have no precise meaning, they are just the outcome of the computation. -/
  let α : ℝ := 12/100
  let L : ℝ := 18 * δ
  let D : ℝ := 55 * δ
  let K₂ : ℝ := α * log 2 / (5 * (4 + (L + 2 * δ)/D) * δ * Λ)
  let K₁ : ℝ := ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp (1/2 * log 2)) * Λ * exp (- ((1 - α) * D * log 2 / (5 * δ))) / K₂)

  calc infDist (f z) G
      ≤ gromovProductAt (f z) (f a) (f b) + 2 * δ := sorry
    _ ≤ (Λ^2 * (D + 3/2 * L + δ + 11/2 * C) - 2 * δ + K₁ * (1 - exp (-K₂ * (b - a)))) + 2 * δ := sorry
    _ = Λ^2 * (D + 3/2 * L + δ + 11/2 * C) + K₁ * (1 - exp (-K₂ * (b - a))) := by ring
    _ ≤ Λ^2 * (D + 3/2 * L + δ + 11/2 * C) + K₁ * (1 - 0) := by
        gcongr
        · dsimp [K₁, L, D]
          ring_nf
          positivity
        · positivity
    _ = Λ^2 * (11/2 * C + (3200 * exp (-(459/50*log 2))/log 2 + 83) * δ) := by
        dsimp [K₁, L, D, α]
        ring_nf
        field_simp
        rw [mul_assoc Λ, ← exp_add]
        ring_nf
    _ ≤ Λ^2 * (11/2 * C + 95 * δ) := by
        gcongr
        have := log_two_gt_d9
        have := exp_one_gt_d9
        calc 3200 * exp (-(459 / 50 * log 2)) / log 2 + 83
            ≤ 3200 * exp (-(459 / 50 * 0.6931471803)) / 0.6931471803 + 83 := by gcongr
          _ ≤ 3200 * exp (-6) / 0.6931471803 + 83 := by
              gcongr
              norm_num
          _ = 3200 * (1 / exp 1 ^ (6 : ℕ)) / 0.6931471803 + 83 := by
              rw [exp_neg]
              field_simp
          _ ≤ 3200 * (1 / 2.7182818283 ^ (6 : ℕ)) / 0.6931471803 + 83 := by gcongr
          _ ≤ 95 := by norm_num1
