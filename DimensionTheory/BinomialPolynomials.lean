/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.LinearAlgebra.Basis.Basic

import DimensionTheory.missing_lemmas.Polynomial
import DimensionTheory.missing_lemmas.Factorial
import DimensionTheory.missing_lemmas.Int

/-!
# Binomial Polynomial

In this file we define binomial polynomials `X choose k` and prove that they form a basis of `F[X]`
over `F` when `F` is a field.

-/

open Polynomial BigOperators Filter
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

/--
The standard difference operator `Δ` is defined as `p ↦ p(X + 1) - p(X)`.
-/

def stdDiffFunc {α β : Type*} [Add α] [One α] [Sub β] (f : α → β) : α → β :=
  fun x ↦ f (x + 1) - f (x)

@[inherit_doc]
scoped[Polynomial] prefix:max "Δᵖ" => stdDiff

@[inherit_doc]
scoped[Function] prefix:max "Δᶠ" => stdDiffFunc

/--iterated standard difference-/
scoped[Polynomial] notation "Δᵖ^[ " n " ] " p => stdDiff^[n] p
/--iterated standard difference-/
scoped[Function] notation "Δᶠ^[ " n " ] " f => stdDiffFunc^[n] f

namespace stdDiffFunc

open Function

lemma eventually_constant_of_stdDiffFunc_eventually_eq_zero_nat
    {α : Type*} [AddGroup α] (f : ℕ → α)
    (hf : ∀ᶠ (m : ℕ) in atTop, Δᶠ f m = 0) :
    ∃ e : α, ∀ᶠ (m : ℕ) in atTop, f m = e := by
  simp only [eventually_atTop, ge_iff_le] at hf ⊢
  obtain ⟨n, hn⟩ := hf
  refine ⟨f n, n, fun m hm => ?_⟩
  have h (k : ℕ) : f n = f (n + k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      specialize hn (n + k) (by norm_num)
      simp only [stdDiffFunc] at hn
      rw [sub_eq_zero] at hn
      rw [← add_assoc, hn, ih]
  rw [show m = n + (m - n) by omega, ← h]

lemma eventually_constant_of_stdDiffFunc_eventually_eq_zero_int
    {α : Type*} [AddGroup α] (f : ℤ → α)
    (hf : ∀ᶠ (m : ℤ) in atTop, Δᶠ f m = 0) :
    ∃ e : α, ∀ᶠ (m : ℤ) in atTop, f m = e := by
  simp only [eventually_atTop, ge_iff_le] at hf ⊢
  obtain ⟨n, hn⟩ := hf
  refine ⟨f n, n, fun m hm => ?_⟩
  have h (k : ℕ) : f n = f (n + k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      specialize hn (n + k) (by norm_num)
      simp only [stdDiffFunc] at hn
      rw [sub_eq_zero] at hn

      rw [Nat.cast_add, ← add_assoc, Nat.cast_one, hn, ih]
  specialize h (m - n).toNat
  rw [Int.coe_toNat_of_nonneg _ (by linarith)] at h
  rw [show m = n + (m - n) by omega, ← h]

end stdDiffFunc

namespace stdDiff

@[simp]
lemma eval_eq (p : R[X]) (x : R) : (Δᵖ p).eval x = p.eval (x + 1) - p.eval x := by simp [stdDiff]

@[simp]
lemma apply_X : Δᵖ (X : R[X]) = 1 := by simp [stdDiff]

@[simp]
lemma apply_C (r : R) : Δᵖ (C r) = 0 := by simp [stdDiff]

lemma pow_apply_C (r : R) (k : ℕ) (hk : 0 < k) : (Δᵖ^[k] (C r)) = 0 := by
  induction k <;> simp_all

@[simp]
lemma apply_constant : Δᵖ (1 : R[X]) = 0 := by simp [stdDiff]

lemma apply_smul (p : R[X]) (r : R) : Δᵖ (r • p) = r • Δᵖ p := by
  ext; simp [mul_sub, stdDiff]

lemma apply_mul (p q : F[X]) : Δᵖ (p * q) = Δᵖ p * (q.comp (X + 1)) + p * Δᵖ q := by
  apply eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem (α := ℕ) (hi := CharZero.cast_injective)
  intro x
  simp only [eval_eq, eval_mul, eval_add, eval_comp, eval_X, eval_one, Set.mem_setOf_eq]
  ring

omit [CharZero F] in
lemma coeff_natDegree_sub_one (p : F[X]) :
    (Δᵖ p).coeff (p.natDegree - 1) = p.natDegree • p.leadingCoeff := by
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
        simp only [mem_support_iff, ne_eq, not_not] at h
        rw [h, zero_mul])
      (by
        intro h
        simp only [mem_support_iff, ne_eq, not_not] at h
        rw [h, zero_mul])]
    simp only [Nat.choose_self, Nat.cast_one, mul_one, coeff_natDegree, add_sub_cancel_left,
      nsmul_eq_mul]
    rw [mul_comm _ p.leadingCoeff]
    congr
    rw [Nat.choose_symm, Nat.choose_one_right]
    omega

omit [CharZero F] in
lemma coeff_natDegree (p : F[X]) : (Δᵖ p).coeff p.natDegree = 0 := by
  have deq1 : (X + 1 : F[X]).natDegree = 1 := by
    rw [show (X + 1 : F[X]) = X + C 1 by simp, natDegree_X_add_C]
  have ceq0 : (X + 1 : F[X]).leadingCoeff = 1 := show coeff _ _ = _ by
    rw [deq1, coeff_add, coeff_X, if_pos rfl, coeff_one, if_neg (by norm_num), add_zero]

  have ceq1 := coeff_comp_degree_mul_degree (p := p) (q := X + 1)
    (by rw [deq1]; simp)
  rw [deq1, mul_one, ceq0, one_pow, mul_one] at ceq1
  simp [stdDiff, ceq1]

omit [CharZero F] in
lemma coeff_eq_zero_of_natDegree_le (p : F[X]) (n : ℕ) (hn : p.natDegree ≤ n) :
    (Δᵖ p).coeff n = 0 := by
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
lemma natDegree_eq (p : F[X]) : (Δᵖ p).natDegree = p.natDegree - 1 := by
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
lemma pow_natDegree_eq (p : F[X]) (k : ℕ) : (Δᵖ^[k] p).natDegree = p.natDegree - k := by
  induction k with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply, natDegree_eq, ih]
    omega

variable {F} in
lemma eventually_eq_zero (p : F[X]) : ∀ᶠ (k : ℕ) in atTop, (Δᵖ^[k] p) = 0 := by
  simp only [eventually_atTop, ge_iff_le]
  refine ⟨p.natDegree + 1, fun m hm => ?_⟩
  apply eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := (↑) '' @Set.univ ℕ) ?_ $ Set.Infinite.image
    (fun _ _ _ _ h => by exact_mod_cast h) Set.infinite_univ
  rintro _ ⟨n, -, rfl⟩
  simp only [eval_zero, Set.mem_setOf_eq]
  have eq0 : (Δᵖ^[p.natDegree] p).natDegree = 0 := by rw [pow_natDegree_eq]; omega
  rw [natDegree_eq_zero] at eq0
  obtain ⟨f, hf⟩ := eq0
  rw [show m = (m - p.natDegree) + p.natDegree by omega]
  rw [Function.iterate_add, Function.comp_apply, ← hf, pow_apply_C, eval_zero]
  omega

variable {F} in
/--
In a field `F` of characteristic zero, let `p` be a polynomial in `F[X]`.
Then `p(n) = ∑ k ∈ {0, ..., p.natDegree}, (Δᵏp)(0) * (n choose k)`.
-/
lemma eval_eq_sum (p : F[X]) (n : ℕ) :
    ∑ k in Finset.range (p.natDegree + 1), (Δᵖ^[k] p).eval 0 * (n.choose k : F)  =
    p.eval (n : F) := by
  induction n generalizing p with
  | zero =>
    simp only [Nat.cast_zero]
    rw [show eval 0 p = eval 0 (Δᵖ^[0] p) * (Nat.choose 0 0 : F) by simp]
    apply Finset.sum_eq_single 0
    · intro k hk1 hk2
      simp only [Finset.mem_range, ne_eq] at hk1 hk2
      rw [Nat.choose_eq_zero_of_lt, Nat.cast_zero, mul_zero]
      omega
    · simp
  | succ n ih =>
    have eq1 : eval (n + 1 : F) p = eval (n : F) (Δᵖ p) + eval (n : F) p := by simp
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

omit [CharZero F] in
@[simp] lemma zeroth : binomialPolynomial F 0 = 1 := by simp [binomialPolynomial]

omit [CharZero F] in
@[simp] lemma first : binomialPolynomial F 1 = X := by simp [binomialPolynomial]

omit [CharZero F] in
lemma succ (k : ℕ) :
    binomialPolynomial F (k + 1) =
    (k + 1 : F)⁻¹ • (binomialPolynomial F k * (X - (C k : F[X]))) := by
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

@[simp]
lemma eval_int_of_le (k : ℕ) (n : ℤ) (h : k ≤ n) :
    eval (n : F) (binomialPolynomial F k) = (n.toNat.choose k : F) := by
  lift n to ℕ
  · linarith

  simp only [Int.cast_natCast, Int.toNat_ofNat]
  rw [eval_of_le F k n]
  norm_cast at h

omit [CharZero F] in
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

lemma eval_neg_nat (k n : ℕ) :
    eval (-n : F) (binomialPolynomial F k) =
    (-1)^k • (n + k - 1).choose k := by
  delta binomialPolynomial
  rw [eval_smul, eval_prod]
  simp_rw [eval_sub, eval_C, eval_X]
  rw [show ∏ x ∈ Finset.range k, (-↑n - ↑x : F) = ∏ x ∈ Finset.range k, (↑n + ↑x) * (-1) from
    Finset.prod_congr rfl fun _ _ => by ring]
  rw [← Finset.prod_mul_pow_card, Finset.card_range]
  rw [show ((n + k - 1).choose k : F) = (k ! : F)⁻¹ * (k ! * (n + k - 1).choose k) by
    rw [← mul_assoc, inv_mul_cancel₀, one_mul]
    exact_mod_cast Nat.factorial_ne_zero _,
    show (k ! * (n + k - 1).choose k : F) = ((k ! * (n + k - 1).choose k : ℕ) : F) by simp,
    ← Nat.ascFactorial_eq_factorial_mul_choose', Nat.ascFactorial_eq_prod_range]
  simp only [smul_eq_mul, Int.reduceNeg, Nat.cast_prod, Nat.cast_add, zsmul_eq_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one]
  ring

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

lemma eval_nat (n k : ℕ) :
    eval (n : F) (binomialPolynomial F k) =
    if k ≤ n then (n.choose k : F) else 0 := by
  split_ifs with h
  · rwa [eval_of_le]
  · rw [eval_of_gt]; linarith

@[simp]
lemma stdDiff_succ (k : ℕ) :
    Δᵖ (binomialPolynomial F (k + 1)) = binomialPolynomial F k := by
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

omit [CharZero F] in
lemma stdDiff_zero : Δᵖ (binomialPolynomial F 0) = 0 := by simp

lemma stdDiff_eq (k : ℕ) :
    Δᵖ (binomialPolynomial F k) =
    if k = 0
    then 0
    else binomialPolynomial F (k - 1) := by
  cases k with
  | zero => simp
  | succ n => simp

variable {F}
/--
In Serre's Local algebra book, this is eₖ(P), where we write the polynomial as
∑ eₖ (X choose k). It can be calculated by Δᵏp (0).
-/
noncomputable abbrev coeff' (p : F[X]) (k : ℕ) : F := (Δᵖ^[k] p).eval 0

omit [CharZero F] in
@[simp] lemma coeff'_zero (p : F[X]) : coeff' p 0 = p.eval 0 := by simp [coeff']

omit [CharZero F] in
lemma coeff'_add (p q : F[X]) (k : ℕ) :
    coeff' (p + q) k = coeff' p k + coeff' q k := by simp [coeff']

omit [CharZero F] in
lemma coeff'_smul (p : F[X]) (r : F) (k : ℕ) :
    coeff' (r • p) k = r * coeff' p k := by
  induction k generalizing p with
  | zero => simp [coeff']
  | succ k ih =>
    simp only [coeff', Function.iterate_succ, Function.comp_apply, stdDiff.apply_smul] at ih ⊢
    rw [ih]

lemma eq_sum_range (p : F[X]) : p =
    ∑ k in Finset.range (p.natDegree + 1), (Δᵖ^[k] p).eval 0 • binomialPolynomial F k := by
  apply eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem (α := Set.Ici (p.natDegree + 2))
    (f := (fun (n : ℕ) ↦ (n : F)) ∘ Subtype.val)
    (hi := CharZero.cast_injective.comp Subtype.val_injective)
  rintro ⟨n, hn⟩
  simp only [Set.mem_Ici] at hn
  simp only [Function.comp_apply, eval_finset_sum, eval_smul, smul_eq_mul, Set.mem_setOf_eq]
  have eq :
      ∑ k ∈ Finset.range (p.natDegree + 1), (Δᵖ^[k] p).eval 0 * eval (↑n) (binomialPolynomial F k) =
      ∑ k ∈ Finset.range (p.natDegree + 1), (Δᵖ^[k] p).eval 0 * (n.choose k : F) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [eval_of_le]
    simp only [Finset.mem_range] at hk
    omega
  rw [eq, stdDiff.eval_eq_sum]

variable (F) in
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

@[simp]
lemma basis_apply (k : ℕ) : basis F k = binomialPolynomial F k := by simp [basis]

/-- antiderivative: the inverse operator to `Δ`, defined by sending `X choose k` to
`X.choose (k + 1)`.-/
noncomputable def antideriv : F[X] →ₗ[F] F[X] :=
(Finsupp.linearCombination _ fun n => binomialPolynomial F (n + 1)) ∘ₗ (basis F).repr.toLinearMap

lemma antideriv_eq_succ (k : ℕ) :
    antideriv (binomialPolynomial F k) =
    binomialPolynomial F (k + 1) := by
  delta antideriv
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  have := (basis F).repr_self k
  rw [basis_apply] at this
  simp only [this, Finsupp.linearCombination_single, one_smul]

lemma antideriv_eq (p : F[X]) :
    antideriv p =
    ∑ k in Finset.range (p.natDegree + 1), (Δᵖ^[k] p).eval 0 • binomialPolynomial F (k + 1) := by
  conv_lhs => rw [eq_sum_range p, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [LinearMapClass.map_smul, antideriv_eq_succ]

@[inherit_doc]
scoped [Polynomial] prefix:max "∫ᵖ" => binomialPolynomial.antideriv

lemma antideriv_stdDiff (p : F[X]) : ∫ᵖ (Δᵖ p) = p - (C $ p.eval 0) := by
  conv_lhs => rw [eq_sum_range p]
  rw [map_sum, map_sum, Finset.sum_range_succ', map_smul, map_smul, stdDiff_zero, map_zero,
    smul_zero, add_zero]
  simp_rw [map_smul, stdDiff_succ, antideriv_eq_succ]
  nth_rw 3 [eq_sum_range p]
  rw [Finset.sum_range_succ']
  simp only [Function.iterate_succ, Function.comp_apply, Function.iterate_zero, id_eq, zeroth]
  rw [add_sub_assoc, show eval 0 p • 1 - C (eval 0 p) = 0 by
    rw [Algebra.smul_def, mul_one, sub_eq_zero]; rfl, add_zero]

lemma stdDiff_antideriv (p : F[X]) : Δᵖ (∫ᵖ p) = p := by
  conv_lhs => rw [eq_sum_range p]
  rw [map_sum, map_sum, Finset.sum_range_succ', map_smul, map_smul]
  simp_rw [map_smul, antideriv_eq_succ, stdDiff_succ]
  conv_rhs => rw [eq_sum_range p]
  rw [Finset.sum_range_succ']


lemma coeff'_natDegree'_ne_zero (p : F[X]) (h : p ≠ 0) : coeff' p p.natDegree ≠ 0 := by
  if h : p.natDegree = 0
  then
    rw [natDegree_eq_zero] at h
    obtain ⟨c, rfl⟩ := h
    rw [natDegree_C, coeff'_zero, eval_C, ne_eq]
    simpa using h
  else

  intro r
  delta coeff' at r
  have := eq_sum_range p

  rw [Finset.sum_range_succ, r, zero_smul, add_zero] at this
  apply_fun natDegree at this
  have ineq := Polynomial.natDegree_sum F (fun i => coeff' p i • binomialPolynomial F i)
      (Finset.range p.natDegree)
  rw [← this] at ineq
  have ineq2 : ((Finset.range p.natDegree).sup fun i =>
    (coeff' p i • binomialPolynomial F i).natDegree) < p.natDegree := by
    rw [Finset.sup_lt_iff]
    pick_goal 2
    · simp only [bot_eq_zero']; omega
    intro i hi
    refine lt_of_le_of_lt (natDegree_smul_le _ _) ?_
    rw [natDegree_eq]
    simpa using hi
  linarith


end binomialPolynomial

namespace stdDiff

variable {F}

lemma natDegree_pow (p : F[X]) (k : ℕ) (hk : k ≤ p.natDegree) :
    (Δᵖ^[k] p).natDegree = p.natDegree - k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply, natDegree_eq, ih (by omega)]
    omega

end stdDiff
