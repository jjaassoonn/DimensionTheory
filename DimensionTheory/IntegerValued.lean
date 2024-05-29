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
  ∀ᶠ (n : ℤ) in atTop, (p.eval n : R) ∈ (algebraMap ℤ R).range

lemma isIntegerValued_def (p : R[X]) :
    IsIntegerValued p ↔ ∀ᶠ (n : ℤ) in atTop, (p.eval n : R) ∈ (algebraMap ℤ R).range := Iff.rfl

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


lemma IsIntegerValued.tfae (p : F[X]) :
    List.TFAE [
      p ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F),
      ∀ (n : ℤ), (p.eval n : F) ∈ (algebraMap ℤ F).range,
      IsIntegerValued p,
      Δ p ∈ Submodule.span ℤ (Set.range <| binomialPolynomial F) ∧
        ∃ (n : ℤ), (p.eval n : F) ∈ (algebraMap ℤ F).range
    ] := by
  tfae_have h12 : 1 → 2
  · apply IsIntegerValued.eval_of_mem_span

  tfae_have h23 : 2 → 3
  · intro h
    simp only [isIntegerValued_def, eventually_iff, mem_atTop_sets, ge_iff_le, Set.mem_setOf_eq]
    refine ⟨0, fun n _ => h n⟩

  tfae_have h14 : 1 → 4
  · exact fun hp => ⟨IsIntegerValued.delta_mem_span_of_mem_span p hp, 0,
      IsIntegerValued.eval_of_mem_span p hp 0⟩

  tfae_have h41 : 4 → 1
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

    rintro ⟨h, ⟨m, ⟨n, hn⟩⟩⟩
    -- rw [mem_span_set] at h
    -- obtain ⟨c, hc, (hp : ∑ i ∈ _, c i • _ = _)⟩ := h
    -- have eq1 := (binomialPolynomial.basis F).total_repr p
    -- apply_fun stdDiff at eq1
    -- rw [← hp] at eq1
    -- change stdDiff (∑ _ ∈ _, _) = _ at eq1
    -- dsimp only [LinearMap.coe_smulRight, LinearMap.id_coe, id_eq] at eq1
    -- have hc' (i : c.support) : ∃ (k : ℕ), i = binomialPolynomial F k := by
    --   obtain ⟨k, hk⟩ := hc i.2
    --   exact ⟨_, hk.symm⟩
    -- choose k hk using hc'
    -- replace hp : Δ p = ∑ i ∈ c.support.attach, c i • binomialPolynomial F (k i) := by
    --   rw [← hp, ← Finset.sum_attach]
    --   refine Finset.sum_congr rfl fun i hi => ?_
    --   rw [hk i]

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
        -- _ = (∑ k ∈ Finset.range, eval 0 (Δ^[k]) - ∑ k ∈ Finset.range, _) + _ := add_sub_comm
    rw [add_sub_right_comm, ← Finset.sum_sub_distrib] at eq1
    simp_rw [← sub_smul, ← eval_sub] at eq1
    rw [sub_eq_iff_eq_add] at eq1
    rw [eq1]
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun k hk => ?_) ?_) h
    · sorry
    · sorry

  tfae_have h31 : 3 → 1
  · sorry

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
def integerValued : Subring F[X] where
  carrier := {p | IsIntegerValued p}
  mul_mem' := IsIntegerValued.mul
  one_mem' := IsIntegerValued.one
  add_mem' := IsIntegerValued.add
  zero_mem' := IsIntegerValued.zero
  neg_mem' := IsIntegerValued.neg

lemma mem_integerValued {p} : p ∈ integerValued F ↔ IsIntegerValued p := Iff.rfl

end Polynomial
