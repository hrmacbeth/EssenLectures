import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith



example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  induction' n with k IH
  · -- base case
    norm_num
  · -- inductive step
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k + 1) := by rel [IH]
      _ = (k + 1 + 1) + k := by ring
      _ ≥ k + 1 + 1 := by linarith


example (n : ℕ) : Even n ∨ Odd n := by
  induction' n with k IH
  · -- base case
    sorry
  · -- inductive step
    obtain ⟨x, hx⟩ | ⟨x, hx⟩ := IH
    · sorry
    · sorry
