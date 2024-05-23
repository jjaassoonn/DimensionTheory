import Mathlib.Algebra.Polynomial.Eval
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Logic.Function.Iterate

open Polynomial BigOperators
open scoped Nat


variable (R : Type*) [CommRing R] (F : Type*) [Field F] [CharZero F]

variable {R} in
/--
The standard difference operator `Δ` is defined as `p ↦ p(X + 1) - p(X)`.
-/
noncomputable def stdDiff : R[X] →+ R[X] where
  toFun p := Polynomial.comp p (X + 1) - p
  map_zero' := by simp
  map_add' p q := by
    ext
    simp only [add_comp, coeff_sub, coeff_add]
    ring

@[inherit_doc]
scoped[Polynomial] prefix:max "Δ" => stdDiff

local notation "Δ^[" n "]" p => stdDiff^[n] p

namespace stdDiff

@[simp]
lemma eval_eq (p : R[X]) (x : R) : (Δ p).eval x = p.eval (x + 1) - p.eval x := by simp [stdDiff]

@[simp]
lemma apply_X : Δ (X : R[X]) = 1 := by simp [stdDiff]

@[simp]
lemma apply_C (r : R) : Δ (C r) = 0 := by simp [stdDiff]

@[simp]
lemma apply_constant : Δ (1 : R[X]) = 0 := by simp [stdDiff]

@[simp]
lemma apply_smul (p : R[X]) (r : R) : Δ (r • p) = r • Δ p := by
  ext; simp [mul_sub, stdDiff]

lemma apply_mul (p q : F[X]) : Δ (p * q) = Δ p * (q.comp (X + 1)) + p * Δ q := by
  apply eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem (α := ℕ) (hi := CharZero.cast_injective)
  intro x
  simp only [eval_eq, eval_mul, eval_add, eval_comp, eval_X, eval_one, Set.mem_setOf_eq]
  ring

variable {F} in
-- if `p` has degree `n`, then `Δ p` has degree `n - 1`. This is because the coefficient of `X^n` in
-- `Δ p` is `0` and the coefficient of `X^(n - 1)` is `p.natDegree * leadingCoeff p`.
lemma natDegree_eq (p : F[X]) : (Δ p).natDegree = p.natDegree - 1 := by sorry

variable {F} in
/--
In a field `F` of characteristic zero, let `p` be a polynomial in `F[X]`.
Then `p(n) = ∑ k ∈ {0, ..., p.natDegree}, (Δᵏp)(0) * (n choose k)`.
-/
lemma eval_eq_sum (p : F[X]) (n : ℕ) :
    ∑ k in Finset.range (p.natDegree + 1), (Δ^[k] p).eval 0 * (n.choose k : F)  =
    p.eval (n : F) := by
  induction n generalizing p with
  | zero =>
    simp only [Nat.cast_zero]
    rw [show eval 0 p = eval 0 (Δ^[0] p) * (Nat.choose 0 0 : F) by simp]
    apply Finset.sum_eq_single 0
    · intro k hk1 hk2
      simp only [Finset.mem_range, ne_eq] at hk1 hk2
      rw [Nat.choose_eq_zero_of_lt, Nat.cast_zero, mul_zero]
      omega
    · simp
  | succ n ih =>
    have eq1 : eval (n + 1 : F) p = eval (n : F) (Δ p) + eval (n : F) p := by simp
    rw [Nat.cast_add, Nat.cast_one, eq1, ← ih, ← ih, natDegree_eq p]
    if h : p.natDegree = 0
    then
      rw [natDegree_eq_zero] at h
      obtain ⟨x, rfl⟩ := h
      simp
    else
      rw [show p.natDegree - 1 + 1 = p.natDegree by omega]
      conv_lhs =>
        rw [Finset.sum_range_succ', Nat.choose_zero_right, Nat.cast_one, mul_one,
          Function.iterate_zero, id]
        simp only [Nat.choose_succ_succ, Nat.cast_add, mul_add]
        rw [Finset.sum_add_distrib]
      conv_rhs =>
        rw [Finset.sum_range_succ', Nat.choose_zero_right, Nat.cast_one, mul_one,
          Function.iterate_zero, id, ← add_assoc]
      rfl

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


@[simp]
lemma eval_of_le (k n : ℕ) (h : k ≤ n) :
    eval (n : F) (binomialPolynomial F k) = (n.choose k : F) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    replace h : k ≤ n ∨ k + 1 = n := by omega
    rcases h with h | rfl
    · simp only [succ, map_natCast, eval_smul, eval_mul, ih _ h, eval_sub, eval_X, eval_natCast,
      smul_eq_mul]
      rw [inv_mul_eq_iff_eq_mul₀]
      pick_goal 2
      · norm_cast
      norm_cast
      rw [mul_comm (k +1), Nat.choose_succ_right_eq]
    · simp only [Nat.cast_add, Nat.cast_one, binomialPolynomial, map_natCast, eval_smul, eval_prod,
      eval_sub, eval_X, eval_natCast, smul_eq_mul, Nat.choose_self]
      rw [inv_mul_eq_iff_eq_mul₀]
      pick_goal 2
      · exact_mod_cast Nat.factorial_ne_zero (k + 1)
      simp only [mul_one]
      have eq1 := Nat.descFactorial_eq_prod_range (k + 1) (k + 1)
      apply_fun fun (x : ℕ) ↦ (x : F) at eq1
      simp only [Nat.cast_prod] at eq1
      convert eq1.symm using 1
      · refine Finset.prod_congr rfl fun j hj ↦ ?_
        simp only [Finset.mem_range] at hj
        rw [Nat.cast_sub, Nat.cast_add, Nat.cast_one]
        omega
      · rw [Nat.descFactorial_self]

@[simp]
lemma stdDiff_succ (k : ℕ) :
    Δ (binomialPolynomial F (k + 1)) = binomialPolynomial F k := by
  apply eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem (α := Set.Ici (k + 2))
    (f := (fun (n : ℕ) ↦ (n : F)) ∘ Subtype.val)
    (hi := CharZero.cast_injective.comp Subtype.val_injective)
  rintro ⟨n, hn⟩
  simp only [Set.mem_Ici] at hn
  simp only [Function.comp_apply, stdDiff, AddMonoidHom.coe_mk, ZeroHom.coe_mk, eval_sub, eval_comp,
    eval_add, eval_X, eval_one, Set.mem_setOf_eq]
  rw [eval_of_le, eval_of_le] <;> try omega

  have := eval_of_le F (k + 1) (n + 1) (by omega)
  simp only [Nat.cast_add, Nat.cast_one] at this
  rw [this]
  rw [sub_eq_iff_eq_add]
  norm_cast

variable {F}
noncomputable abbrev coeff' (p : F[X]) (k : ℕ) : F := (Δ^[k] p).eval 0

@[simp]
lemma coeff'_zero (p : F[X]) : coeff' p 0 = p.eval 0 := by simp [coeff']

lemma coeff'_add (p q : F[X]) (k : ℕ) :
    coeff' (p + q) k = coeff' p k + coeff' q k := by simp [coeff']

lemma coeff'_smul (p : F[X]) (r : F) (k : ℕ) :
    coeff' (r • p) k = r * coeff' p k := by
  induction k generalizing p with
  | zero => simp [coeff']
  | succ k ih =>
    simp only [coeff', Function.iterate_succ, Function.comp_apply, stdDiff.apply_smul] at ih ⊢
    rw [ih]

lemma eq_sum_range (p : F[X]) : p =
    ∑ k in Finset.range (p.natDegree + 1), (Δ^[k] p).eval 0 • binomialPolynomial F k := by
  apply eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem (α := Set.Ici (p.natDegree + 2))
    (f := (fun (n : ℕ) ↦ (n : F)) ∘ Subtype.val)
    (hi := CharZero.cast_injective.comp Subtype.val_injective)
  rintro ⟨n, hn⟩
  simp only [Set.mem_Ici] at hn
  simp only [Function.comp_apply, eval_finset_sum, eval_smul, smul_eq_mul, Set.mem_setOf_eq]
  have eq :
      ∑ k ∈ Finset.range (p.natDegree + 1), (Δ^[k] p).eval 0 * eval (↑n) (binomialPolynomial F k) =
      ∑ k ∈ Finset.range (p.natDegree + 1), (Δ^[k] p).eval 0 * (n.choose k : F) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [eval_of_le]
    simp only [Finset.mem_range] at hk
    omega
  rw [eq, stdDiff.eval_eq_sum]

/--
the set of binomial polynomials `X choose k` is a basis for `F[X]`.
-/
noncomputable def basis : Basis ℕ F F[X] :=
  .mk (v := binomialPolynomial F)
    (by
      rw [linearIndependent_iff']
      intro s g hg
      sorry)
    (fun x _ ↦ eq_sum_range x ▸ Submodule.sum_mem _ fun k hk ↦ Submodule.smul_mem _ _ $
      Submodule.subset_span ⟨k, rfl⟩)

end binomialPolynomial
