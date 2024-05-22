import Mathlib.Algebra.Polynomial.Eval
import Mathlib.Data.Nat.Factorial.Basic

open Polynomial BigOperators
open scoped Nat


variable (R : Type*) [CommRing R] (F : Type*) [Field F] [CharZero F]

variable {R} in
/--
The standard difference operator `Δ` is defined as `p ↦ p(X + 1) - p(X)`.
-/
noncomputable abbrev stdDiff (p : R[X]) : R[X] :=
  Polynomial.comp p (X + 1) - p

@[inherit_doc]
scoped[Polynomial] prefix:max "Δ" => stdDiff

namespace stdDiff

@[simp high]
lemma eval_eq (p : R[X]) (x : R) : (Δ p).eval x = p.eval (x + 1) - p.eval x := by simp

end stdDiff

/--
the `k`-th binomial polynomial is `X choose k`
-/
noncomputable def binomialPolynomial (k : ℕ) : F[X] :=
  (k ! : F)⁻¹ • ∏ i ∈ Finset.range k, (X - (C i : F[X]))

namespace binomialPolynomial

@[simp]
lemma zeroth : binomialPolynomial F 0 = 1 := by simp [binomialPolynomial]

@[simp]
lemma first : binomialPolynomial F 1 = X := by simp [binomialPolynomial]

lemma succ (k : ℕ) :
    binomialPolynomial F (k + 1) = (k + 1 : F)⁻¹ • (binomialPolynomial F k * (X - (C k : F[X]))) := by
  simp only [binomialPolynomial, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    mul_inv_rev, map_natCast, Finset.prod_range_succ, ← smul_mul_assoc, mul_smul, nsmul_eq_mul]
  rw [← mul_smul, mul_comm _ (k + 1 : F)⁻¹, mul_smul]

lemma stdDiff_succ (k : ℕ) :
    Δ (binomialPolynomial F (k + 1)) = binomialPolynomial F k := by
  rcases k with _ | k
  · ext; simp
  · sorry

end binomialPolynomial
