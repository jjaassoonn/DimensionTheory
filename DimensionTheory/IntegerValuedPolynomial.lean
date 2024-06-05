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
    Δ p ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F) := by
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
    (Δ^[k] p) ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F) := by
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
    (delta_p_mem : Δ p ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F))
    (n : ℤ) :
    p.eval (n : F) ∈ (algebraMap ℤ F).range ↔ p.eval (n + 1 : F) ∈ (algebraMap ℤ F).range := by
  have h1 : (Δ p).eval (n : F) ∈ (algebraMap ℤ F).range :=
    IsIntegerValued.eval_of_mem_span _ delta_p_mem n
  have eq1 : p.eval (n + 1 : F) - p.eval (n : F) = (Δ p).eval (n : F) := by simp
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
    (delta_p_mem : Δ p ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F))
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
    (delta_p_mem : Δ p ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F))
    (n : ℤ) :
    p.eval (n : F) ∈ (algebraMap ℤ F).range ↔ p.eval (n - 1 : F) ∈ (algebraMap ℤ F).range := by
  have h1 : (Δ p).eval (n - 1 : F) ∈ (algebraMap ℤ F).range := by
    convert IsIntegerValued.eval_of_mem_span _ delta_p_mem (n - 1)
    simp
  have eq1 : p.eval (n : F) - p.eval (n - 1 : F) = (Δ p).eval (n - 1 : F) := by simp
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
    (delta_p_mem : Δ p ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F))
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
    (delta_p_mem : Δ p ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F)) :
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
    Δ p ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F) ∧
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
      have eq_delta_p := binomialPolynomial.eq_sum_range (Δ p)
      replace eq_delta_p := calc Δ p
          _ = _ := eq_delta_p
          _ = ∑ k ∈ Finset.range p.natDegree, _ := Finset.sum_congr (by
            rw [stdDiff.natDegree_eq]
            congr
            refine Nat.succ_pred_eq_of_pos $ show 0 < p.natDegree by omega) fun _ _ ↦ rfl
          _ = ∑ k ∈ Finset.range p.natDegree, eval 0 (Δ^[k+1] p) • binomialPolynomial F k :=
              Finset.sum_congr rfl fun k _ => by simp
      rw [Finset.sum_range_succ] at eq_p
      have eq1 := calc p - Δ p
          _ = (∑ _ ∈ _, _ + _) - (∑ _ ∈ _, _) := congr_arg₂ (· - ·) eq_p eq_delta_p
      rw [add_sub_right_comm, ← Finset.sum_sub_distrib] at eq1
      simp_rw [← sub_smul, ← eval_sub] at eq1
      rw [sub_eq_iff_eq_add] at eq1
      rw [eq1]
      refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun k hk => ?_) ?_) h1
      · suffices mem : eval 0 ((Δ^[k] p) - Δ^[k + 1] p) ∈ (algebraMap ℤ F).range by
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
            have h2 := IsIntegerValued.delta_pow_mem_span_of_mem_span (Δ p) h1 k
            replace h2 := IsIntegerValued.eval_of_mem_span _ h2 0
            simpa using h2
        · rw [Function.iterate_succ, Function.comp_apply]
          have h2 := IsIntegerValued.delta_pow_mem_span_of_mem_span (Δ p) h1 k
          replace h2 := IsIntegerValued.eval_of_mem_span _ h2 0
          simpa using h2
      · suffices mem : eval 0 (Δ^[p.natDegree] p) ∈ (algebraMap ℤ F).range by
          rcases mem with ⟨j, hj⟩
          rw [← hj, Polynomial.smul_eq_C_mul]
          convert_to j • binomialPolynomial F p.natDegree ∈ _
          · simp
          · exact Submodule.smul_mem _ _ $ Submodule.subset_span ⟨p.natDegree, rfl⟩
        cases p.natDegree with
        | zero => simpa using h2 0
        | succ k =>
          rw [Function.iterate_succ, Function.comp_apply]
          have h2 := IsIntegerValued.delta_pow_mem_span_of_mem_span (Δ p) h1 k
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
    specialize ih (Δ p) (by
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
      IsIntegerValued Δ p ∧
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
    IsIntegerValued (Δ p) := by
  have := IsIntegerValued.tfae p |>.out 2 3 |>.mp hp
  exact this.1

instance IsIntegerValued.stdDiff_pow {p : F[X]} [hp : IsIntegerValued p] (n : ℕ) :
    IsIntegerValued (Δ^[n] p) := by
  induction n with
  | zero => simpa
  | succ n ih =>
    rw [Function.iterate_succ']
    exact ih.stdDiff

instance IsIntegerValued.antideriv {p : F[X]} [hp : IsIntegerValued p] :
    IsIntegerValued (∫ p) := by
  have := IsIntegerValued.tfae (∫ p) |>.out 2 3
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
    (f.coeffInt i : F) = (Δ^[i] f).eval 0 :=
  IsIntegerValued.coeff'_in_int f i |>.choose_spec

lemma eq_sum_range (f : F[X]) [IsIntegerValued f]:
    f =
    ∑ k in Finset.range (f.natDegree + 1), f.coeffInt k • binomialPolynomial F k := by
  conv_lhs => rw [binomialPolynomial.eq_sum_range f]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [zsmul_eq_mul, ← coeffInt_spec, Algebra.smul_def]
  rfl

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

open Asymptotics
open scoped Nat

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

-- example (f : F[X]) [hf : IsIntegerValued f] :
--     ((↑) : ℤ → ℚ) ∘ f.evalInt ~[atTop]
--     fun n => f.coeffInt f.natDegree • (n^f.natDegree / f.natDegree !) := by
--   if hdeg : f.natDegree = 0
--   then
--     simp only [hdeg, pow_zero, Nat.factorial_zero, Nat.cast_one, ne_eq, one_ne_zero,
--       not_false_eq_true, div_self, zsmul_eq_mul, mul_one]
--     change _ ~[atTop] Function.const _ (f.coeffInt 0 : ℚ)
--     rw [natDegree_eq_zero] at hdeg
--     obtain ⟨c, rfl⟩ := hdeg
--     rw [IsIntegerValued.iff_forall] at hf
--     specialize hf 0
--     simp only [Int.cast_zero, eval_C, algebraMap_int_eq, RingHom.mem_range, eq_intCast] at hf
--     obtain ⟨c, rfl⟩ := hf
--     if hc : c = 0
--     then
--       subst hc
--       conver Int.cast ∘ (0 : F[X]).evalInt ~[atTop] Function.const _ 0
--       simp only [Int.cast_zero, map_zero]
--       sorry
--     else
--     have : (C (c : F)).evalInt ~[atTop] Function.const _ c := by
--       rw [isEquivalent_const_iff_tendsto]
--     rw [show (C (c : F)).evalInt =[atTop] Function.const _ c by
--       ext x
--       simp only [map_intCast, Function.const_apply]
--       apply_fun ((↑) : ℤ → F) using Int.cast_injective
--       rw [evalInt_spec']
--       pick_goal 2
--       · simp only [natDegree_intCast, CharP.cast_eq_zero]; norm_num
--       simp only [natDegree_intCast, zero_add, Finset.range_one, smul_eq_mul, Finset.sum_singleton,
--         Nat.choose_zero_right, Nat.cast_one, mul_one, Int.cast_inj]

--       letI : (c : F[X]).IsIntegerValued := sorry
--       apply_fun ((↑) : ℤ → F) using Int.cast_injective
--       rw [coeffInt_spec]
--       simp only [Function.iterate_zero, id_eq, eval_intCast]
--       ]
--     rw [isEquivalent_const_iff_tendsto, tendsto_iff_forall_eventually_mem]
--     intro s hs
--     simp only [Function.comp_apply, eventually_atTop, ge_iff_le] at hs ⊢
--     rw [mem_nhds_iff] at hs

--     sorry
--   else

--   rw [Asymptotics.isEquivalent_iff_tendsto_one]
--   · sorry
--   · simp only [zsmul_eq_mul, ne_eq, mul_eq_zero, Int.cast_eq_zero, div_eq_zero_iff,
--       pow_eq_zero_iff', Nat.cast_eq_zero, not_or, not_and, Decidable.not_not, eventually_atTop,
--       ge_iff_le]
--     refine ⟨f.natDegree, fun n hn => ⟨?_, by rintro rfl; simpa using hn,
--       f.natDegree.factorial_ne_zero⟩⟩

--     intro rid
--     have := f.eq_sum_range
--     rw [Finset.sum_range_succ, rid, zero_smul, add_zero] at this
--     apply_fun natDegree at this
--     have ineq := Polynomial.natDegree_sum F (fun i => f.coeffInt i • binomialPolynomial F i)
--       (Finset.range f.natDegree)
--     rw [← this] at ineq
--     have := Finset.le_sup
--     sorry


-- lemma coeff_natDegree_pos_iff_eval_eventually_pos
--     (f : F[X]) [hf : IsIntegerValued f] :
--     0 < f.coeffInt (f.natDegree) ↔
--     ∀ᶠ (n : ℤ) in atTop, 0 < (f.evalInt n) := by
--   constructor
--   · have := eq_sum_range f
--     sorry
--   · sorry

end Polynomial
