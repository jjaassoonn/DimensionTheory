import DimensionTheory.BinomialPolynomials
import Mathlib.Order.Filter.AtTopBot

open Filter BigOperators

variable (R F : Type*) [CommRing R] [Field F] [CharZero F]

namespace Polynomial

variable {R F}

/--
Serre's Local algebra, page 21, lemma 2 (probably needs char 0 fields)

A polynomial `p` is integer valued if any of the following equivalent condition holds:
1. `p` is a `ℤ`-linear combination of binomial polynomials
2. `p` evaluates to an integer for all integer inputs
3. `p` evaluates to an integer for all sufficiently large integer inputs
4. `Δp` is integer valued and `p(n)` is integer for at least one integer `n`
-/
def IsIntegerValued (p : R[X]) : Prop :=
  ∀ᶠ (n : ℕ) in atTop, (p.eval n : R) ∈ (algebraMap ℤ R).range

lemma isIntegerValued_def (p : R[X]) :
    IsIntegerValued p ↔ ∀ᶠ (n : ℕ) in atTop, (p.eval n : R) ∈ (algebraMap ℤ R).range := Iff.rfl

lemma iIntegerValued_tfae (p : F[X]) :
    List.TFAE [
      p ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F),
      ∀ (n : ℕ), (p.eval n : F) ∈ (algebraMap ℤ F).range,
      IsIntegerValued p,
      IsIntegerValued (Δ p) ∧ ∃ (n : ℕ), (p.eval n : F) ∈ (algebraMap ℤ F).range
    ] := by
  tfae_have 1 → 2
  · intro h
    rw [mem_span_set] at h
    obtain ⟨c, hc, rfl⟩ := h
    intro m

    rw [Finsupp.sum, eval_finset_sum]
    refine Subring.sum_mem _ fun i hi => ?_
    rw [eval_smul, zsmul_eq_mul]
    specialize hc hi
    obtain ⟨k, rfl⟩ := hc
    have := binomialPolynomial.eval_of_le F k m
    refine Subring.mul_mem _ (by simp) ?_
    if le : k ≤ m
    then
      rw [binomialPolynomial.eval_of_le _ _ _ le]
      exact ⟨m.choose k, by simp⟩
    else
      rw [binomialPolynomial.eval_of_gt _ _ _ (by simpa using le)]
      simp

  tfae_have 2 → 3
  · intro h
    simp only [isIntegerValued_def, eventually_iff, mem_atTop_sets, ge_iff_le, Set.mem_setOf_eq]
    refine ⟨0, fun n _ => h n⟩


  sorry

end Polynomial
