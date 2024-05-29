import Mathlib.Order.Filter.AtTopBot

import DimensionTheory.BinomialPolynomials
import DimensionTheory.missing_lemmas.Int

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
  ∀ᶠ (n : ℤ) in atTop, (p.eval n : R) ∈ (algebraMap ℤ R).range

lemma isIntegerValued_def (p : R[X]) :
    IsIntegerValued p ↔ ∀ᶠ (n : ℤ) in atTop, (p.eval n : R) ∈ (algebraMap ℤ R).range := Iff.rfl

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

lemma IsIntegerValued.iff_forall (p : F[X]) :
    IsIntegerValued p ↔  ∀ (n : ℤ), (p.eval n : F) ∈ (algebraMap ℤ F).range :=
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
/--
The collection of integer-valued polynomials forms a subring.
-/
def integerValued : Subring F[X] where
  carrier := {p | IsIntegerValued p}
  mul_mem' := IsIntegerValued.mul
  one_mem' := IsIntegerValued.one
  add_mem' := IsIntegerValued.add
  zero_mem' := IsIntegerValued.zero
  neg_mem' := IsIntegerValued.neg

lemma mem_integerValued {p} : p ∈ integerValued F ↔ IsIntegerValued p := Iff.rfl

end Polynomial
