import Mathlib.Tactic.Ring

theorem p2_smoke (a b : ℤ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

#print axioms p2_smoke
