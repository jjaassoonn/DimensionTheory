/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import DimensionTheory.BinomialPolynomials
import DimensionTheory.missing_lemmas.Int

import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Integer Valued Polynomial

Serre's Local algebra, page 21, lemma 2

A polynomial `p` is integer valued if any of the following equivalent condition holds:
1. `p` is a `ℤ`-linear combination of binomial polynomials
2. `p` evaluates to an integer for all integer inputs
3. `p` evaluates to an integer for all sufficiently large integer inputs
4. `Δp` is integer valued and `p(n)` is integer for at least one integer `n`

-/

open Filter BigOperators

variable (R F : Type*) [CommRing R] [Field F] [CharZero F]

namespace Polynomial

variable {R F}

/--
Serre's Local algebra, page 21, lemma 2

A polynomial `p` is integer valued if any of the following equivalent condition holds:
1. `p` is a `ℤ`-linear combination of binomial polynomials
2. `p` evaluates to an integer for all integer inputs
3. `p` evaluates to an integer for all sufficiently large integer inputs
4. `Δp` is integer valued and `p(n)` is integer for at least one integer `n`
-/
class IsIntegerValued (p : R[X]) : Prop where
  out : ∀ᶠ (n : ℤ) in atTop, (p.eval n : R) ∈ (algebraMap ℤ R).range

lemma isIntegerValued_def (p : R[X]) :
    IsIntegerValued p ↔ ∀ᶠ (n : ℤ) in atTop, (p.eval n : R) ∈ (algebraMap ℤ R).range :=
  ⟨fun h => h.out, fun h => ⟨h⟩⟩

lemma isIntegerValued_def' (p : R[X]) :
    IsIntegerValued p ↔
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → (p.eval n : R) ∈ (algebraMap ℤ R).range := by
  rw [isIntegerValued_def]; simp

lemma IsIntegerValued.delta_mem_span_of_mem_span
    (p : F[X]) (hp : p ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F)) :
    Δᵖ p ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F) := by
  rw [mem_span_set] at hp
  obtain ⟨c, hc, (rfl : ∑ _ ∈ _, _ • _ = _)⟩ := hp
  rw [map_sum]
  simp_rw [map_zsmul]
  refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ ?_
  specialize hc hk
  obtain ⟨k, rfl⟩ := hc
  cases k with
  | zero => simp
  | succ k =>
    rw [binomialPolynomial.stdDiff_succ]
    refine Submodule.subset_span ⟨k, rfl⟩

lemma IsIntegerValued.delta_pow_mem_span_of_mem_span
    (p : F[X]) (hp : p ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F)) (k : ℕ) :
    (Δᵖ^[k] p) ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F) := by
  induction k with
  | zero => simpa
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    exact IsIntegerValued.delta_mem_span_of_mem_span _ ih

lemma IsIntegerValued.eval_of_mem_span
    (p : F[X]) (hp : p ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F)) (x : ℤ) :
    eval (x : F) p ∈ (algebraMap ℤ F).range := by
  rw [mem_span_set] at hp
  obtain ⟨c, hc, rfl⟩ := hp
  rw [Finsupp.sum, eval_finset_sum]
  refine Subring.sum_mem _ fun i hi => ?_
  rw [eval_smul, zsmul_eq_mul]
  specialize hc hi
  obtain ⟨k, rfl⟩ := hc
  refine Subring.mul_mem _ (by simp) ?_
  if le : k ≤ x
  then
    rw [binomialPolynomial.eval_int_of_le F k x le]
    exact ⟨x.toNat.choose k, by simp⟩
  else
    if h : x < 0
    then
      rw [show x = -(-x).toNat by
        induction x with
        | ofNat x => norm_cast at h
        | negSucc x => rw [Int.neg_negSucc]; rfl]
      simp only [Int.cast_neg, Int.cast_natCast, binomialPolynomial.eval_neg_nat, Int.reduceNeg,
        zsmul_eq_mul, Int.cast_pow, Int.cast_one, algebraMap_int_eq, RingHom.mem_range, eq_intCast]
      refine ⟨(-1)^k * ((-x).toNat + k - 1).choose k, by simp⟩
    else

    lift x to ℕ
    · linarith
    simp only [Int.cast_natCast, algebraMap_int_eq, RingHom.mem_range, eq_intCast]
    rw [binomialPolynomial.eval_of_gt _ _ _ (by simpa using le)]
    simp

lemma IsIntegerValued.eval_add_one_of_delta_mem_span
    (p : F[X])
    (delta_p_mem : Δᵖ p ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F))
    (n : ℤ) :
    p.eval (n : F) ∈ (algebraMap ℤ F).range ↔ p.eval (n + 1 : F) ∈ (algebraMap ℤ F).range := by
  have h1 : (Δᵖ p).eval (n : F) ∈ (algebraMap ℤ F).range :=
    IsIntegerValued.eval_of_mem_span _ delta_p_mem n
  have eq1 : p.eval (n + 1 : F) - p.eval (n : F) = (Δᵖ p).eval (n : F) := by simp
  rw [sub_eq_iff_eq_add] at eq1
  rw [eq1]
  fconstructor
  · intro h
    exact Subring.add_mem _ h1 h
  · intro h
    convert Subring.sub_mem _ h h1
    simp

lemma IsIntegerValued.eval_add_of_delta_mem_span
    (p : F[X])
    (delta_p_mem : Δᵖ p ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F))
    (n : ℤ) (k : ℕ) :
    p.eval (n : F) ∈ (algebraMap ℤ F).range ↔ p.eval (n + k : F) ∈ (algebraMap ℤ F).range := by
  induction k with
  | zero => simp
  | succ k ih =>
    have := IsIntegerValued.eval_add_one_of_delta_mem_span p
      delta_p_mem (n + k)
    simp only [Int.cast_add, Int.cast_natCast] at this
    rw [this] at ih
    rw [ih]
    congr! 2
    simp only [Nat.cast_add, Nat.cast_one, add_assoc]

lemma IsIntegerValued.eval_sub_one_of_delta_mem_span
    (p : F[X])
    (delta_p_mem : Δᵖ p ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F))
    (n : ℤ) :
    p.eval (n : F) ∈ (algebraMap ℤ F).range ↔ p.eval (n - 1 : F) ∈ (algebraMap ℤ F).range := by
  have h1 : (Δᵖ p).eval (n - 1 : F) ∈ (algebraMap ℤ F).range := by
    convert IsIntegerValued.eval_of_mem_span _ delta_p_mem (n - 1)
    simp
  have eq1 : p.eval (n : F) - p.eval (n - 1 : F) = (Δᵖ p).eval (n - 1 : F) := by simp
  rw [sub_eq_iff_eq_add] at eq1
  rw [eq1]
  fconstructor
  · intro h
    convert Subring.sub_mem _ h h1
    simp
  · intro h
    exact Subring.add_mem _ h1 h

lemma IsIntegerValued.eval_sub_of_delta_mem_span
    (p : F[X])
    (delta_p_mem : Δᵖ p ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F))
    (n : ℤ) (k : ℕ) :
    p.eval (n : F) ∈ (algebraMap ℤ F).range ↔ p.eval (n - k : F) ∈ (algebraMap ℤ F).range := by
  induction k with
  | zero => simp
  | succ k ih =>
    have := IsIntegerValued.eval_sub_one_of_delta_mem_span p
      delta_p_mem (n - k)
    simp only [Int.cast_sub, Int.cast_natCast] at this
    rw [this] at ih
    rw [ih]
    congr! 2
    simp only [Nat.cast_add, Nat.cast_one]
    abel

lemma IsIntegerValued.exists_iff_forall_of_delta_mem_span
    (p : F[X])
    (delta_p_mem : Δᵖ p ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F)) :
    (∀ (n : ℤ), p.eval (n : F) ∈ (algebraMap ℤ F).range) ↔
    (∃ (n : ℤ), p.eval (n : F) ∈ (algebraMap ℤ F).range) := by
  constructor
  · intro h; exact ⟨0, h _⟩
  · rintro ⟨n, hn⟩ m
    if hmn : m ≤ n
    then
      rw [show (m : F) = (n - (n - m) : F) by abel]
      rw [IsIntegerValued.eval_sub_of_delta_mem_span p delta_p_mem n (n - m).toNat] at hn
      convert hn using 2
      norm_cast
      rw [show ((n - m).toNat : ℤ) = n - m by rw [Int.coe_toNat_of_nonneg]; linarith]
    else
      simp only [not_le] at hmn
      rw [show (m : F) = (n + (m - n)) by abel]
      rw [IsIntegerValued.eval_add_of_delta_mem_span p delta_p_mem n (m - n).toNat] at hn
      convert hn using 2
      norm_cast
      rw [show ((m - n).toNat : ℤ) = m - n by rw [Int.coe_toNat_of_nonneg]; linarith]

lemma IsIntegerValued.mem_span_iff_delta_mem_span_and_integer_point (p : F[X]) :
    p ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F) ↔
    Δᵖ p ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F) ∧
        ∃ (n : ℤ), (p.eval n : F) ∈ (algebraMap ℤ F).range := by
  constructor
  · exact fun hp => ⟨IsIntegerValued.delta_mem_span_of_mem_span p hp, 0,
      IsIntegerValued.eval_of_mem_span p hp 0⟩
  · if h_p_deg : p.natDegree = 0
    then
      rw [natDegree_eq_zero] at h_p_deg
      obtain ⟨r, rfl⟩ := h_p_deg
      simp only [stdDiff.apply_C, Submodule.zero_mem, eval_C, algebraMap_int_eq, RingHom.mem_range,
        eq_intCast, exists_const, true_and, forall_exists_index]
      rintro z rfl
      rw [show C (z : F) = z • 1 by simp]
      exact Submodule.smul_mem _ _ <| Submodule.subset_span ⟨0, by simp⟩
    else
      rintro ⟨h1, h2⟩
      rw [← IsIntegerValued.exists_iff_forall_of_delta_mem_span p h1] at h2
      have eq_p := binomialPolynomial.eq_sum_range p
      have eq_delta_p := binomialPolynomial.eq_sum_range (Δᵖ p)
      replace eq_delta_p := calc Δᵖ p
          _ = _ := eq_delta_p
          _ = ∑ k ∈ Finset.range p.natDegree, _ := Finset.sum_congr (by
            rw [stdDiff.natDegree_eq]
            congr
            refine Nat.succ_pred_eq_of_pos $ show 0 < p.natDegree by omega) fun _ _ ↦ rfl
          _ = ∑ k ∈ Finset.range p.natDegree, eval 0 (Δᵖ^[k+1] p) • binomialPolynomial F k :=
              Finset.sum_congr rfl fun k _ => by simp
      rw [Finset.sum_range_succ] at eq_p
      have eq1 := calc p - Δᵖ p
          _ = (∑ _ ∈ _, _ + _) - (∑ _ ∈ _, _) := congr_arg₂ (· - ·) eq_p eq_delta_p
      rw [add_sub_right_comm, ← Finset.sum_sub_distrib] at eq1
      simp_rw [← sub_smul, ← eval_sub] at eq1
      rw [sub_eq_iff_eq_add] at eq1
      rw [eq1]
      refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun k hk => ?_) ?_) h1
      · suffices mem : eval 0 ((Δᵖ^[k] p) - Δᵖ^[k + 1] p) ∈ (algebraMap ℤ F).range by
          rcases mem with ⟨j, hj⟩
          rw [← hj, Polynomial.smul_eq_C_mul]
          convert_to j • binomialPolynomial F k ∈ _
          · simp
          · exact Submodule.smul_mem _ _ $ Submodule.subset_span ⟨k, rfl⟩

        rw [eval_sub]
        refine Subring.sub_mem _ ?_ ?_
        · simp only [Finset.mem_range] at hk
          cases k with
          | zero =>
            simp only [Function.iterate_zero, id_eq]
            simpa using h2 0
          | succ k =>
            rw [Function.iterate_succ, Function.comp_apply]
            have h2 := IsIntegerValued.delta_pow_mem_span_of_mem_span (Δᵖ p) h1 k
            replace h2 := IsIntegerValued.eval_of_mem_span _ h2 0
            simpa using h2
        · rw [Function.iterate_succ, Function.comp_apply]
          have h2 := IsIntegerValued.delta_pow_mem_span_of_mem_span (Δᵖ p) h1 k
          replace h2 := IsIntegerValued.eval_of_mem_span _ h2 0
          simpa using h2
      · suffices mem : eval 0 (Δᵖ^[p.natDegree] p) ∈ (algebraMap ℤ F).range by
          rcases mem with ⟨j, hj⟩
          rw [← hj, Polynomial.smul_eq_C_mul]
          convert_to j • binomialPolynomial F p.natDegree ∈ _
          · simp
          · exact Submodule.smul_mem _ _ $ Submodule.subset_span ⟨p.natDegree, rfl⟩
        cases p.natDegree with
        | zero => simpa using h2 0
        | succ k =>
          rw [Function.iterate_succ, Function.comp_apply]
          have h2 := IsIntegerValued.delta_pow_mem_span_of_mem_span (Δᵖ p) h1 k
          replace h2 := IsIntegerValued.eval_of_mem_span _ h2 0
          simpa using h2

lemma IsIntegerValued.mem_span {p : F[X]} (iv : IsIntegerValued p) :
    p ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F) := by
  suffices ind :
      ∀ (n : ℕ) (p : F[X]), IsIntegerValued p → p.natDegree ≤ n →
        p ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F) by
    exact ind p.natDegree p iv (le_refl _)
  apply Nat.rec
  · simp only [Nat.zero_eq, nonpos_iff_eq_zero]
    intro p iv hp
    rw [Polynomial.natDegree_eq_zero] at hp
    obtain ⟨m, rfl⟩ := hp
    rw [isIntegerValued_def'] at iv
    obtain ⟨N, hN⟩ := iv
    specialize hN N (le_refl _)
    simp only [eval_C, algebraMap_int_eq, RingHom.mem_range, eq_intCast] at hN
    obtain ⟨x, rfl⟩ := hN
    convert_to x • binomialPolynomial F 0 ∈ _
    · simp
    · exact Submodule.smul_mem _ _ $ Submodule.subset_span ⟨0, rfl⟩
  · intro n ih p iv p_deg
    simp only [Nat.succ_eq_add_one] at p_deg
    specialize ih (Δᵖ p) (by
      rw [isIntegerValued_def'] at iv ⊢
      obtain ⟨N, hN⟩ := iv
      refine ⟨N, fun n hn => ?_⟩
      rw [stdDiff.eval_eq]
      refine Subring.sub_mem _ ?_ ?_
      · have := hN (n + 1) (by omega)
        simpa using this
      · exact hN _ hn) (by rw [stdDiff.natDegree_eq]; omega)
    rw [IsIntegerValued.mem_span_iff_delta_mem_span_and_integer_point]
    refine ⟨ih, ?_⟩
    rw [isIntegerValued_def'] at iv
    obtain ⟨N, hN⟩ := iv
    exact ⟨N, hN N $ le_refl _⟩

/--
Lemma II.B.1 from Serre's Local Algebra.
-/
lemma IsIntegerValued.tfae (p : F[X]) :
    List.TFAE [
      p ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F),
      ∀ (n : ℤ), (p.eval n : F) ∈ (algebraMap ℤ F).range,
      IsIntegerValued p,
      IsIntegerValued Δᵖ p ∧
        ∃ (n : ℤ), (p.eval n : F) ∈ (algebraMap ℤ F).range
    ] := by

  tfae_have 1 → 2
  · apply IsIntegerValued.eval_of_mem_span

  tfae_have 2 → 3
  · intro h
    simp only [isIntegerValued_def, eventually_iff, mem_atTop_sets, ge_iff_le, Set.mem_setOf_eq]
    refine ⟨0, fun n _ => h n⟩

  tfae_have 3 → 1
  · apply IsIntegerValued.mem_span

  tfae_have 1 → 4
  · intro h
    rw [IsIntegerValued.mem_span_iff_delta_mem_span_and_integer_point] at h
    refine ⟨?_, h.2⟩
    rw [isIntegerValued_def']
    exact ⟨0, fun n _ => IsIntegerValued.eval_of_mem_span _ h.1 _⟩

  tfae_have 4 → 1
  · intro h
    rw [IsIntegerValued.mem_span_iff_delta_mem_span_and_integer_point]
    exact ⟨h.1.mem_span, h.2⟩

  tfae_finish

open IsIntegerValued

instance (k : ℕ) : IsIntegerValued (binomialPolynomial F k) := by
  have := IsIntegerValued.tfae (binomialPolynomial F k) |>.out 2 0
  rw [this]
  exact Submodule.subset_span ⟨k, rfl⟩

lemma IsIntegerValued.iff_forall (p : F[X]) :
    IsIntegerValued p ↔  ∀ (n : ℤ), (p.eval n : F) ∈ (algebraMap ℤ F).range :=
  tfae p |>.out 2 1

-- this is true in any commutative ring as well. Here I am being lazy by assuming field.
instance IsIntegerValued.add {p q : F[X]} [hp : IsIntegerValued p] [hq : IsIntegerValued q] :
    IsIntegerValued (p + q) := by
  rw [iff_forall] at *
  intro n
  rw [eval_add]
  exact Subring.add_mem _ (hp n) (hq n)

-- this is true in any commutative ring as well. Here I am being lazy by assuming field.
instance IsIntegerValued.mul {p q : F[X]} [hp : IsIntegerValued p] [hq : IsIntegerValued q] :
    IsIntegerValued (p * q) := by
  rw [iff_forall] at *
  intro n
  rw [eval_mul]
  exact Subring.mul_mem _ (hp n) (hq n)

-- this is true in any commutative ring as well. Here I am being lazy by assuming field.
instance IsIntegerValued.zero : IsIntegerValued (0 : F[X]) := by
  rw [iff_forall]; intro; simp

-- this is true in any commutative ring as well. Here I am being lazy by assuming field.
protected lemma IsIntegerValued.one : IsIntegerValued (1 : F[X]) := by
  rw [iff_forall]; intro; simp

-- this is true in any commutative ring as well. Here I am being lazy by assuming field.
instance IsIntegerValued.neg {p : F[X]} [hp : IsIntegerValued p] :
    IsIntegerValued (-p : F[X]) := by
  rw [iff_forall] at *
  intro n
  rw [eval_neg]
  exact Subring.neg_mem _ (hp n)

instance IsIntegerValued.stdDiff {p : F[X]} [hp : IsIntegerValued p] :
    IsIntegerValued (Δᵖ p) := by
  have := IsIntegerValued.tfae p |>.out 2 3 |>.mp hp
  exact this.1

instance IsIntegerValued.stdDiff_pow {p : F[X]} [hp : IsIntegerValued p] (n : ℕ) :
    IsIntegerValued (Δᵖ^[n] p) := by
  induction n with
  | zero => simpa
  | succ n ih =>
    rw [Function.iterate_succ']
    exact ih.stdDiff

instance IsIntegerValued.antideriv {p : F[X]} [hp : IsIntegerValued p] :
    IsIntegerValued (∫ᵖ p) := by
  have := IsIntegerValued.tfae (∫ᵖ p) |>.out 2 3
  rw [this]
  rw [binomialPolynomial.stdDiff_antideriv]
  refine ⟨hp, 0, ?_⟩
  rw [binomialPolynomial.antideriv_eq, eval_finset_sum]
  simp_rw [eval_smul, smul_eq_mul]
  refine Subring.sum_mem _ fun i _ => Subring.mul_mem _ ?_ ?_
  · have := hp.stdDiff_pow i
    rw [iff_forall] at this
    simpa using this 0
  · rw [Int.cast_zero]
    rw [binomialPolynomial.eval_zero]
    simp

variable (F) in
/--
The collection of integer-valued polynomials forms a subring.
-/
def integerValued : Subring F[X] where
  carrier := {p | IsIntegerValued p}
  mul_mem' hp hq := IsIntegerValued.mul (hp := hp) (hq := hq)
  one_mem' := IsIntegerValued.one
  add_mem' hp hq := IsIntegerValued.add (hp := hp) (hq := hq)
  zero_mem' := IsIntegerValued.zero
  neg_mem' hp := IsIntegerValued.neg (hp := hp)

lemma mem_integerValued {p} : p ∈ integerValued F ↔ IsIntegerValued p := Iff.rfl

lemma IsIntegerValued.coeff'_in_int (f : F[X]) [hf : IsIntegerValued f] (i : ℕ) :
    binomialPolynomial.coeff' f i ∈ (algebraMap ℤ F).range := by
  simpa using (IsIntegerValued.iff_forall _ |>.1 $ hf.stdDiff_pow i) 0

noncomputable def coeffInt {f : F[X]} [IsIntegerValued f] (i : ℕ) : ℤ :=
  IsIntegerValued.coeff'_in_int f i |>.choose

lemma coeffInt_spec {f : F[X]} [IsIntegerValued f] (i : ℕ) :
    (f.coeffInt i : F) = (Δᵖ^[i] f).eval 0 :=
  IsIntegerValued.coeff'_in_int f i |>.choose_spec

lemma eq_sum_range (f : F[X]) [IsIntegerValued f]:
    f =
    ∑ k in Finset.range (f.natDegree + 1), f.coeffInt k • binomialPolynomial F k := by
  conv_lhs => rw [binomialPolynomial.eq_sum_range f]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [zsmul_eq_mul, ← coeffInt_spec, Algebra.smul_def]
  rfl

lemma coeffInt_natDegree_ne_zero (f : F[X]) [IsIntegerValued f] (hf : f ≠ 0) :
    f.coeffInt f.natDegree ≠ 0 := by
  apply_fun ((↑) : ℤ → F) using Int.cast_injective
  rw [coeffInt_spec]
  simpa using binomialPolynomial.coeff'_natDegree'_ne_zero f hf

lemma coeffInt_zero (k : ℕ) : (0 : F[X]).coeffInt k = 0 := by
  apply_fun ((↑) : ℤ → F) using Int.cast_injective
  rw [coeffInt_spec]
  simp

noncomputable def evalInt (f : F[X]) [hf : IsIntegerValued f] (n : ℤ) : ℤ :=
  IsIntegerValued.iff_forall _ |>.1 hf n |>.choose

lemma evalInt_spec (f : F[X]) [hf : IsIntegerValued f] (n : ℤ) :
    (f.evalInt n : F) = (f.eval n : F) :=
  IsIntegerValued.iff_forall _ |>.1 hf n |>.choose_spec

lemma evalInt_spec' (f : F[X]) [IsIntegerValued f] (n : ℤ) (hn : f.natDegree ≤ n) :
    f.evalInt n =
    ∑ i in Finset.range (f.natDegree + 1), f.coeffInt i • (n.toNat.choose i : ℤ) := by
  apply_fun ((↑) : ℤ → F) using Int.cast_injective
  rw [evalInt_spec]
  conv_lhs => rw [eq_sum_range f, eval_finset_sum]
  simp_rw [eval_smul]
  simp only [zsmul_eq_mul, smul_eq_mul, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  rw [binomialPolynomial.eval_int_of_le]
  omega

lemma evalInt_spec'' (f : F[X]) [IsIntegerValued f] (n : ℤ) (hn : f.natDegree ≤ n) :
    f.evalInt n =
    f.coeffInt f.natDegree • (n.toNat.choose f.natDegree : ℤ) +
    ∑ i in Finset.range (f.natDegree), f.coeffInt i • (n.toNat.choose i : ℤ) := by
  rwa [evalInt_spec', Finset.sum_range_succ, add_comm]

lemma evalInt_zero (n : ℤ) :
    (0 : F[X]).evalInt n = 0 := by
  apply_fun ((↑) : ℤ → F) using Int.cast_injective
  rw [evalInt_spec]
  simp

section Asymptotics

open Asymptotics
open scoped Nat

variable (F) in
lemma binomialPolynomial_eval_equivalent (k : ℕ) :
    (↑) ∘ (binomialPolynomial F k).evalInt ~[atTop]
    fun n => (n^k / k ! : ℚ) := by
  refine IsEquivalent.trans ?_ $ Nat.choose_isEquivalent_atTop_int k
  rw [isEquivalent_iff_tendsto_one]
  · rw [tendsto_iff_forall_eventually_mem]
    intro s hs
    simp only [Pi.div_apply, Function.comp_apply, eventually_atTop, ge_iff_le]
    refine ⟨k, fun n hn => ?_⟩
    have eq1 : (binomialPolynomial F k).evalInt n = (n.toNat.choose k : ℤ) := by
      apply_fun ((↑) : ℤ → F) using Int.cast_injective
      rw [evalInt_spec]
      rw [binomialPolynomial.eval_int_of_le]
      pick_goal 2
      · assumption
      simp
    rw [eq1]
    simp only [Int.cast_natCast]
    rw [div_self]
    pick_goal 2
    · simp only [ne_eq, Nat.cast_eq_zero]
      intro r
      rw [Nat.choose_eq_zero_iff] at r
      apply_fun ((↑) : ℕ → ℤ) at r using Nat.mono_cast (α := ℤ)
      simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at r
      rw [Int.coe_toNat_of_nonneg] at r
      · omega
      · omega

    exact mem_of_mem_nhds hs
  · simp only [ne_eq, div_eq_zero_iff, pow_eq_zero_iff', Int.cast_eq_zero, Nat.cast_eq_zero,
      not_or, not_and, Decidable.not_not, eventually_atTop, ge_iff_le]
    refine ⟨k, fun n hn => ?_⟩
    intro r
    rw [Nat.choose_eq_zero_iff] at r
    apply_fun ((↑) : ℕ → ℤ) at r using Nat.mono_cast (α := ℤ)
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at r
    rw [Int.coe_toNat_of_nonneg] at r
    · omega
    · omega


lemma isEquivalent_leading_monomial (f : F[X]) [hf : IsIntegerValued f] :
    (fun n : ℤ => (f.evalInt n : ℚ)) ~[atTop]
    fun n : ℤ =>
      f.coeffInt f.natDegree • (binomialPolynomial F f.natDegree).evalInt n := by
  if hf : f = 0
  then
    subst hf
    simp only [evalInt_zero, Int.cast_zero, natDegree_zero, coeffInt_zero,
      binomialPolynomial.zeroth, zero_smul]
    rfl
  else
  have eq1 :
    (fun n : ℤ => (f.evalInt n : ℚ)) =ᶠ[atTop]
    fun n => f.coeffInt f.natDegree • (n.toNat.choose f.natDegree : ℤ) +
      ∑ i in Finset.range (f.natDegree), f.coeffInt i • (n.toNat.choose i : ℤ) := by
    change ∀ᶠ _ in _, _
    simp only [Int.cast_natCast, zsmul_eq_mul, smul_eq_mul, Int.cast_sum, Int.cast_mul,
      eventually_atTop, ge_iff_le]
    refine ⟨f.natDegree, fun b hb => ?_⟩
    rw [evalInt_spec'' (hn := hb)]
    simp only [smul_eq_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_sum]

  have isequiv1 :
    (fun n : ℤ => (f.coeffInt f.natDegree • (n.toNat.choose f.natDegree : ℤ) +
      ∑ i in Finset.range (f.natDegree), f.coeffInt i • (n.toNat.choose i : ℤ) : ℚ)) ~[atTop]
    fun n : ℤ =>
      (f.coeffInt f.natDegree • (binomialPolynomial F f.natDegree).evalInt n : ℚ) := by

    apply IsEquivalent.add_isLittleO
    · simp only [Int.cast_natCast, zsmul_eq_mul]
      apply IsEquivalent.mul
      · rfl
      · refine IsEquivalent.trans ?_ $ binomialPolynomial_eval_equivalent F f.natDegree |>.symm
        apply Nat.choose_isEquivalent_atTop_int

    · simp only [smul_eq_mul, Int.cast_sum, Int.cast_mul, Int.cast_natCast, zsmul_eq_mul]
      apply Asymptotics.IsLittleO.sum
      intro i hi
      simp only [Finset.mem_range] at hi
      if hi : f.coeffInt i = 0
      then
        rw [hi]
        simp only [Int.cast_zero, zero_mul, isLittleO_const_left, true_or]
      else
        rw [isLittleO_const_mul_right_iff, isLittleO_const_mul_left_iff]
        pick_goal 2
        · exact_mod_cast hi

        pick_goal 2
        · simp only [ne_eq, Int.cast_eq_zero]
          intro rid
          exact coeffInt_natDegree_ne_zero f hf rid

        calc (fun x : ℤ => (x.toNat.choose i : ℚ))
          _ ~[atTop] fun x : ℤ => (x^i / i ! : ℚ) := Nat.choose_isEquivalent_atTop_int _
          _ =o[atTop] fun x : ℤ => (x^f.natDegree / i ! : ℚ) := by
            rw [isLittleO_iff_exists_eq_mul]
            refine ⟨fun x => (x : ℚ)^(-(f.natDegree - i : ℕ) : ℤ), ?_, ?_⟩
            · simp only [zpow_neg, zpow_natCast]
              apply Tendsto.inv_tendsto_atTop
              change Tendsto ((fun x : ℚ => x ^ (f.natDegree - i)) ∘ ((↑) : ℤ → ℚ)) _ _
              fapply Filter.Tendsto.comp
              · exact atTop
              · apply tendsto_pow_atTop
                omega
              · exact tendsto_intCast_atTop_atTop

            change ∀ᶠ _ in _, _
            simp only [zpow_neg, zpow_natCast, Pi.mul_apply, eventually_atTop, ge_iff_le]
            refine ⟨1, fun n hn => ?_⟩
            field_simp
            rw [← mul_assoc]
            congr
            rw [← pow_add, ← Nat.add_sub_assoc, Nat.add_sub_cancel_left]
            omega
          _ =O[atTop] fun x : ℤ => (x^f.natDegree / f.natDegree ! : ℚ) := by
            rw [isBigO_atTop_iff_eventually_exists]
            simp only [ge_iff_le, norm, Rat.cast_div, Rat.cast_pow, Rat.cast_intCast,
              Rat.cast_natCast, eventually_atTop]
            refine ⟨1, fun n hn => ⟨f.natDegree ! / i !, fun m hm => ?_⟩⟩
            rw [abs_of_nonneg, abs_of_nonneg]
            pick_goal 2
            · apply div_nonneg <;> norm_cast
              · apply pow_nonneg; linarith
              · linarith
            rw [div_mul_eq_mul_div, mul_div_cancel₀]
            · norm_cast; exact Nat.factorial_ne_zero f.natDegree
            · apply div_nonneg <;> norm_cast
              · apply pow_nonneg; linarith
              · linarith
          _ ~[atTop] fun x : ℤ => ((binomialPolynomial F f.natDegree).evalInt x : ℚ) := by
            symm; apply binomialPolynomial_eval_equivalent

  exact IsEquivalent.congr_left isequiv1 eq1.symm

lemma isEquivalent_leading_monomial' (f : F[X]) [hf : IsIntegerValued f] :
    ((↑) : ℤ → ℚ) ∘ f.evalInt ~[atTop]
    fun n => f.coeffInt f.natDegree • (n^f.natDegree / f.natDegree !) := by
  refine f.isEquivalent_leading_monomial.trans ?_
  simp only [zsmul_eq_mul]
  apply IsEquivalent.mul
  · rfl
  · apply binomialPolynomial_eval_equivalent F f.natDegree

end Asymptotics

lemma coeff_natDegree_pos_iff_eval_eventually_pos
    (f : F[X]) [hf : IsIntegerValued f] :
    0 < f.coeffInt (f.natDegree) ↔
    ∀ᶠ (n : ℤ) in atTop, 0 < (f.evalInt n) := by
  constructor
  · intro H
    have : _ =o[_] _ := isEquivalent_leading_monomial f
    rw [Asymptotics.IsLittleO_def] at this
    specialize this (c := 1/2) (by simp)
    rw [Asymptotics.IsBigOWith_def] at this
    simp only [zsmul_eq_mul, Pi.sub_apply, norm_mul, Int.norm_cast_rat, eventually_atTop,
      ge_iff_le] at this ⊢
    obtain ⟨a, ha⟩ := this
    refine ⟨max f.natDegree a, fun b hb => ?_⟩
    specialize ha b (by aesop)
    lift b to ℕ
    · simp only [max_le_iff] at hb
      omega
    simp only [one_div] at ha
    change |_| ≤ 2⁻¹ * (|_| * |_|) at ha
    simp only [Rat.cast_sub, Rat.cast_intCast, Rat.cast_mul] at ha
    rw [abs_le, abs_of_nonneg, abs_of_nonneg] at ha
    pick_goal 2
    · norm_cast
      have eq : ((binomialPolynomial F f.natDegree).evalInt b : F) =
          (b.choose f.natDegree : F) := by

        rw [evalInt_spec]
        rw [show ((b : ℤ) : F) = (b : F) by aesop, binomialPolynomial.eval_of_le F]
        simp only [max_le_iff, Nat.cast_le] at hb
        exact hb.1
      norm_cast at eq
      rw [eq]
      norm_cast
      exact Nat.zero_le (b.choose f.natDegree)
    pick_goal 2
    · norm_cast; omega
    obtain ⟨ha, -⟩ := ha
    simp only [neg_le_sub_iff_le_add] at ha
    rw [← sub_le_iff_le_add, inv_mul_eq_div, sub_half, div_le_iff₀] at ha
    pick_goal 2
    · exact zero_lt_two
    norm_cast at ha
    suffices 0 < f.evalInt b * 2 by omega
    refine lt_of_lt_of_le ?_ ha
    apply mul_pos
    · exact H
    norm_cast
    have eq : ((binomialPolynomial F f.natDegree).evalInt b : F) =
        (b.choose f.natDegree : F) := by

      rw [evalInt_spec]
      rw [show ((b : ℤ) : F) = (b : F) by aesop, binomialPolynomial.eval_of_le F]
      simp only [max_le_iff, Nat.cast_le] at hb
      exact hb.1
    norm_cast at eq
    rw [eq]
    norm_cast
    apply Nat.choose_pos
    simp only [max_le_iff, Nat.cast_le] at hb
    exact hb.1
  · intro h
    simp only [eventually_atTop, ge_iff_le] at h
    obtain ⟨N, hN⟩ := h
    have : _ =o[_] _ := isEquivalent_leading_monomial f
    rw [Asymptotics.IsLittleO_def] at this
    specialize this (c := 1) (by simp)
    rw [Asymptotics.IsBigOWith_def] at this
    simp only [zsmul_eq_mul, Pi.sub_apply, one_div, norm_mul, Int.norm_cast_rat, eventually_atTop,
      ge_iff_le, gt_iff_lt] at this ⊢
    obtain ⟨M, hM⟩ := this
    specialize hN (max f.natDegree <| max M N) (by simp)
    specialize hM (max f.natDegree <| max M N) (by simp)
    change |_| ≤ 1 * (|_| * |_|) at hM
    simp only [Rat.cast_sub, Rat.cast_intCast, Rat.cast_mul, one_mul] at hM
    rw [abs_le] at hM
    obtain ⟨-, hM⟩ := hM
    simp only [tsub_le_iff_right] at hM
    by_contra! ineq
    norm_cast at hM
    rw [abs_of_nonpos ineq, abs_of_nonneg] at hM
    pick_goal 2
    · norm_cast
      have eq : ((binomialPolynomial F f.natDegree).evalInt (max f.natDegree <| max M N) : F) =
          (max f.natDegree <| (max M N).toNat).choose f.natDegree := by


        rw [show (max f.natDegree <| max M N : ℤ) = (max f.natDegree <| (max M N).toNat : ℕ) by
          simp only [Nat.cast_max]
          by_cases h : f.natDegree ≤ (max M N)
          · rw [max_eq_right]
            rw [max_eq_right (a := (f.natDegree : ℤ))]
            rw [Int.toNat_of_nonneg]
            · refine le_trans ?_ h
              norm_cast
              exact Nat.zero_le f.natDegree
            · rwa [Int.toNat_of_nonneg]
              refine le_trans ?_ h
              norm_cast
              exact Nat.zero_le f.natDegree
            · assumption
          simp only [le_max_iff, not_or, not_le] at h
          rw [max_eq_left, max_eq_left (a := (f.natDegree : ℤ))]
          · norm_cast
            rw [Int.toNat_le]
            simp only [max_le_iff]
            omega
          · omega]
        rw [evalInt_spec]
        rw [show (((max f.natDegree <| (max M N).toNat : ℕ) : ℤ) : F) =
            ((max f.natDegree <| (max M N).toNat : ℕ) : F) by norm_cast]
        rw [binomialPolynomial.eval_of_le F]
        exact Nat.le_max_left _ _
      norm_cast at eq
      rw [eq]
      norm_cast
      exact Nat.zero_le _
    simp only [neg_mul, neg_add_cancel] at hM
    linarith

end Polynomial
