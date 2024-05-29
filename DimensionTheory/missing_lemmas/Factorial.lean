import Mathlib.Data.Nat.Factorial.BigOperators

open BigOperators Nat

theorem Nat.ascFactorial_eq_prod_range (n k : ℕ) :
    n.ascFactorial k = ∏ i in Finset.range k, (n + i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [ascFactorial_succ, ih, Finset.prod_range_succ, mul_comm]

theorem Nat.right_factorial_dvd_ascFactorial (n k : ℕ) :
    k ! ∣ n.ascFactorial k := by
  rw [ascFactorial_eq_factorial_mul_choose']
  simp
