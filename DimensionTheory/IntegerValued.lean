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

lemma IsIntegerValued.tfae (p : F[X]) :
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

open IsIntegerValued

lemma IsIntegerValued.iff_forall (p : F[X]) :
    IsIntegerValued p ↔  ∀ (n : ℕ), (p.eval n : F) ∈ (algebraMap ℤ F).range :=
  tfae p |>.out 2 1

-- this is true in any commutative ring as well. Here I am being lazy by assuming field.
protected lemma IsIntegerValued.add {p q : F[X]} (hp : IsIntegerValued p) (hq : IsIntegerValued q) :
    IsIntegerValued (p + q) := by
  rw [iff_forall] at *
  intro n
  rw [eval_add]
  exact Subring.add_mem _ (hp n) (hq n)

-- this is true in any commutative ring as well. Here I am being lazy by assuming field.
protected lemma IsIntegerValued.mul {p q : F[X]} (hp : IsIntegerValued p) (hq : IsIntegerValued q) :
    IsIntegerValued (p * q) := by
  rw [iff_forall] at *
  intro n
  rw [eval_mul]
  exact Subring.mul_mem _ (hp n) (hq n)

-- this is true in any commutative ring as well. Here I am being lazy by assuming field.
protected lemma IsIntegerValued.zero : IsIntegerValued (0 : F[X]) := by
  rw [iff_forall]; intro; simp

-- this is true in any commutative ring as well. Here I am being lazy by assuming field.
protected lemma IsIntegerValued.one : IsIntegerValued (1 : F[X]) := by
  rw [iff_forall]; intro; simp

-- this is true in any commutative ring as well. Here I am being lazy by assuming field.
protected lemma IsIntegerValued.neg {p : F[X]} (hp : IsIntegerValued p) :
    IsIntegerValued (-p : F[X]) := by
  rw [iff_forall] at *
  intro n
  rw [eval_neg]
  exact Subring.neg_mem _ (hp n)

variable (F) in
def integerValued : Subring F[X] where
  carrier := {p | IsIntegerValued p}
  mul_mem' := IsIntegerValued.mul
  one_mem' := IsIntegerValued.one
  add_mem' := IsIntegerValued.add
  zero_mem' := IsIntegerValued.zero
  neg_mem' := IsIntegerValued.neg

lemma mem_integerValued {p} : p ∈ integerValued F ↔ IsIntegerValued p := Iff.rfl

end Polynomial
