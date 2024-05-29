import Mathlib.Algebra.Polynomial.Eval
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Logic.Function.Iterate

import DimensionTheory.missing_lemmas.PolynomialLinearIndependent

open Polynomial BigOperators
open scoped Nat


variable (R : Type*) [CommRing R] (F : Type*) [Field F] [CharZero F]

variable {R} in
/--
The standard difference operator `Δ` is defined as `p ↦ p(X + 1) - p(X)`.
-/
noncomputable def stdDiff : R[X] →ₗ[R] R[X] where
  toFun p := Polynomial.comp p (X + 1) - p
  map_smul' r p := by
    ext n
    simp only [smul_comp, coeff_sub, coeff_smul, smul_eq_mul, RingHom.id_apply, mul_sub]
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

lemma coeff_natDegree_sub_one (p : F[X]) :
    (Δ p).coeff (p.natDegree - 1) = p.natDegree • p.leadingCoeff := by
  if h : p.natDegree = 0
  then
    rw [natDegree_eq_zero] at h
    obtain ⟨c, rfl⟩ := h
    simp
  else
    simp only [stdDiff, LinearMap.coe_mk, AddHom.coe_mk, coeff_sub, nsmul_eq_mul]
    rw [comp_eq_sum_left, coeff_sum]
    simp_rw [coeff_C_mul, coeff_X_add_one_pow F]
    rw [sum_def]
    rw [Finset.sum_eq_add (p.natDegree - 1) p.natDegree (by omega)
      (by
        rintro i hi0 ⟨hi1, hi2⟩
        replace hi0 := p.supp_subset_range_natDegree_succ hi0
        simp only [Finset.mem_range] at hi0
        have hi : i < p.natDegree - 1 := by omega
        rw [Nat.choose_eq_zero_of_lt hi, Nat.cast_zero, mul_zero])
      (by
        intro h
        simp only [mem_support_iff, ne_eq, Decidable.not_not] at h
        rw [h, zero_mul])
      (by
        intro h
        simp only [mem_support_iff, ne_eq, Decidable.not_not] at h
        rw [h, zero_mul])]
    simp only [Nat.choose_self, Nat.cast_one, mul_one, coeff_natDegree, add_sub_cancel_left,
      nsmul_eq_mul]
    rw [mul_comm _ p.leadingCoeff]
    congr
    rw [Nat.choose_symm, Nat.choose_one_right]
    omega

lemma coeff_natDegree (p : F[X]) : (Δ p).coeff p.natDegree = 0 := by
  have deq1 : (X + 1 : F[X]).natDegree = 1 := by
    rw [show (X + 1 : F[X]) = X + C 1 by simp, natDegree_X_add_C]
  have ceq0 : (X + 1 : F[X]).leadingCoeff = 1 := show coeff _ _ = _ by
    rw [deq1, coeff_add, coeff_X, if_pos rfl, coeff_one, if_neg (by norm_num), add_zero]

  have ceq1 := coeff_comp_degree_mul_degree (p := p) (q := X + 1)
    (by rw [deq1]; simp)
  rw [deq1, mul_one, ceq0, one_pow, mul_one] at ceq1
  simp [stdDiff, ceq1]


lemma coeff_eq_zero_of_natDegree_le (p : F[X]) (n : ℕ) (hn : p.natDegree ≤ n) :
    (Δ p).coeff n = 0 := by
  rw [le_iff_eq_or_lt] at hn
  rcases hn with rfl | hn
  · apply coeff_natDegree
  have deq1 : (X + 1 : F[X]).natDegree = 1 := by
    rw [show (X + 1 : F[X]) = X + C 1 by simp, natDegree_X_add_C]

  have deq2 := natDegree_comp (p := p) (q := X + 1)
  rw [deq1, mul_one] at deq2

  simp only [stdDiff, LinearMap.coe_mk, AddHom.coe_mk, coeff_sub]
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_eq_zero_of_natDegree_lt, sub_zero]
  all_goals aesop

variable {F} in
-- if `p` has degree `n`, then `Δ p` has degree `n - 1`. This is because the coefficient of `X^n` in
-- `Δ p` is `0` and the coefficient of `X^(n - 1)` is `p.natDegree * leadingCoeff p`.
lemma natDegree_eq (p : F[X]) : (Δ p).natDegree = p.natDegree - 1 := by
  if p_ne_zero : p = 0
  then
      subst p_ne_zero
      simp
  else if p_ne_C : ∃ r, p = C r
  then
    obtain ⟨r, rfl⟩ := p_ne_C
    simp
  else
  rw [natDegree_eq_of_le_of_coeff_ne_zero]
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro n hn
    apply coeff_eq_zero_of_natDegree_le
    omega
  · rw [coeff_natDegree_sub_one]
    simp only [nsmul_eq_mul, ne_eq, mul_eq_zero, Nat.cast_eq_zero, leadingCoeff_eq_zero, p_ne_zero,
      or_false]
    contrapose! p_ne_zero
    rw [natDegree_eq_zero] at p_ne_zero
    tauto



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


lemma ne_zero (k : ℕ) : binomialPolynomial F k ≠ 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [succ]
    simp only [map_natCast, ne_eq, smul_eq_zero, inv_eq_zero, mul_eq_zero, not_or]
    exact ⟨by norm_cast, ih, X_sub_C_ne_zero (k : F)⟩

lemma natDegree_eq (k : ℕ) : (binomialPolynomial F k).natDegree = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [succ, natDegree_smul_of_smul_regular]
    pick_goal 2
    · intro x y (hxy : _ • _ = _ • _)
      simp only [smul_eq_mul, mul_eq_mul_left_iff, inv_eq_zero] at hxy
      exact hxy.resolve_right (by norm_cast)

    rw [natDegree_mul (hp := ne_zero _ _) (hq := X_sub_C_ne_zero (k : F)),
      natDegree_X_sub_C, ih]

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

lemma eval_of_gt (k n : ℕ) (h : k > n) :
    eval (n : F) (binomialPolynomial F k) = 0 := by
  delta binomialPolynomial
  simp only [map_natCast, eval_smul, smul_eq_mul]
  rw [eval_prod]
  simp_rw [eval_sub, eval_X, eval_natCast]
  suffices eq1 : ∏ x ∈ Finset.range k, (n - x : F) = 0 by
    rw [eq1, mul_zero]
  fapply Finset.prod_eq_zero
  · exact n
  · simpa
  · simp

lemma eval_zero (k : ℕ) :
    eval 0 (binomialPolynomial F k) =
    if k = 0 then 1 else 0 := by
  if h : k = 0
  then
    subst h
    simp
  else
    rw [if_neg h]
    simpa using eval_of_gt F k 0 (by omega)

@[simp]
lemma stdDiff_succ (k : ℕ) :
    Δ (binomialPolynomial F (k + 1)) = binomialPolynomial F k := by
  apply eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem (α := Set.Ici (k + 2))
    (f := (fun (n : ℕ) ↦ (n : F)) ∘ Subtype.val)
    (hi := CharZero.cast_injective.comp Subtype.val_injective)
  rintro ⟨n, hn⟩
  simp only [Set.mem_Ici] at hn
  simp only [Function.comp_apply, stdDiff, LinearMap.coe_mk, AddHom.coe_mk, eval_sub, eval_comp,
    eval_add, eval_X, eval_one, Set.mem_setOf_eq]
  rw [eval_of_le, eval_of_le] <;> try omega

  have := eval_of_le F (k + 1) (n + 1) (by omega)
  simp only [Nat.cast_add, Nat.cast_one] at this
  rw [this]
  rw [sub_eq_iff_eq_add]
  norm_cast

variable {F}
/--
In Serre's Local algebra book, this is eₖ(P), where we write the polynomial as
∑ eₖ (X choose k). It can be calculated by Δᵏp (0).
-/
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
      apply linearIndependent_of_degree_distinct (ne_zero := ne_zero F)
      intro i j hij hd
      rw [degree_eq_natDegree (ne_zero _ _), degree_eq_natDegree (ne_zero _ _),
        natDegree_eq, natDegree_eq] at hd
      exact hij (by exact_mod_cast hd))
    (fun x _ ↦ eq_sum_range x ▸ Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ $
      Submodule.subset_span ⟨k, rfl⟩)

end binomialPolynomial
