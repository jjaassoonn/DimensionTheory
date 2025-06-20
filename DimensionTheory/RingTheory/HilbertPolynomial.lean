/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/

import DimensionTheory.missing_lemmas.Factorial
import DimensionTheory.missing_lemmas.InvOneSubPow

import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Div

/-!
# Hilbert polynomials

Given any `p : ℤ[X]` and `d : ℕ`, there exists some `h : ℚ[X]` such that for any
large enough `n : ℕ`, `PowerSeries.coeff ℤ n (p * invOneSubPow ℤ d)` is equal to
`h.eval (n : ℚ)`. This `h` is unique and is called the Hilbert polynomial with
respect to `p` and `d` (`Polynomial.hilbert p d`).

I simplified some proofs in the original file done by John
-/

open BigOperators
open PowerSeries

namespace Polynomial

section greatestFactorOneSubNotDvd

variable {R : Type*} [CommRing R] [NeZero (1 : R)] [NoZeroDivisors R]
variable (p : R[X]) (hp : p ≠ 0) (d : ℕ)

/--
Given a polynomial `p`, the greatest factor of `p` that is not divided by `1 - X`.
-/
noncomputable def greatestFactorOneSubNotDvd : R[X] :=
  ((- 1 : R[X]) ^ p.rootMultiplicity 1) *
  (exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 1).choose

local notation "gFOSND" => greatestFactorOneSubNotDvd

omit [NeZero (1 : R)] [NoZeroDivisors R] in
theorem pow_rootMultiplicity_mul_greatestFactorOneSubNotDvd_eq :
    ((1 - X : R[X]) ^ p.rootMultiplicity 1) * greatestFactorOneSubNotDvd p hp = p := by
  rw [greatestFactorOneSubNotDvd, ← mul_assoc, ← mul_pow]
  simp only [mul_neg, mul_one, neg_sub, map_one]
  exact id (exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 1).choose_spec.1.symm

omit [NeZero (1 : R)] [NoZeroDivisors R] in
theorem greatestFactorOneSubNotDvd_ne_zero :
    greatestFactorOneSubNotDvd p hp ≠ 0 := fun h0 => by
  let hpow := pow_rootMultiplicity_mul_greatestFactorOneSubNotDvd_eq p hp
  rw [h0, mul_zero] at hpow; exact hp <| id hpow.symm

theorem natDegree_greatestFactorOneSubNotDvd_le :
    (greatestFactorOneSubNotDvd p hp).natDegree ≤ p.natDegree := by
  have : p.natDegree = ((1 - X : R[X]) ^ p.rootMultiplicity 1 * gFOSND p hp).natDegree := by
    rw [pow_rootMultiplicity_mul_greatestFactorOneSubNotDvd_eq]
  rw [this, natDegree_mul]
  exact (gFOSND p hp).natDegree.le_add_left (natDegree ((1 - X) ^ p.rootMultiplicity 1))
  exact pow_ne_zero _ <| fun h0 => by
    let this : (1 - X : R[X]).coeff 0 = 0 := by rw [h0]; simp only [coeff_zero];
    simp only [coeff_sub, coeff_one_zero, coeff_X_zero, sub_zero, one_ne_zero] at this
  exact greatestFactorOneSubNotDvd_ne_zero p hp

theorem natDegree_pow_rootMultiplicity_sub_mul_greatestFactorOneSubNotDvd_le
    (hp1 : d ≤ p.rootMultiplicity 1) :
    ((1 - X) ^ ((p.rootMultiplicity 1) - d) * greatestFactorOneSubNotDvd p hp).natDegree
    ≤ p.natDegree := by
  let this := pow_ne_zero (p.rootMultiplicity 1 - d) <| fun (h0 : (1 - X : R[X]) = 0) => by
    let this : (1 - X : R[X]).coeff 0 = 0 := by rw [h0, coeff_zero];
    simp only [coeff_sub, coeff_one_zero, coeff_X_zero, sub_zero, one_ne_zero] at this
  rw [show p.natDegree = (((1 - X : R[X]) ^ (p.rootMultiplicity 1 - d + d)) *
    gFOSND p hp).natDegree by rw [← Nat.eq_add_of_sub_eq hp1 rfl,
    pow_rootMultiplicity_mul_greatestFactorOneSubNotDvd_eq], pow_add, mul_assoc,
    mul_comm ((1 - X) ^ d), ← mul_assoc, natDegree_mul, natDegree_mul, natDegree_mul]
  simp only [natDegree_pow, le_add_iff_nonneg_right, zero_le]
  · exact this
  · exact greatestFactorOneSubNotDvd_ne_zero p hp
  · rw [mul_ne_zero_iff]; exact ⟨this, greatestFactorOneSubNotDvd_ne_zero p hp⟩
  · exact pow_ne_zero _ <| fun h0 => by
      let this : (1 - X : R[X]).coeff 0 = 0 := by rw [h0, coeff_zero];
      simp only [coeff_sub, coeff_one_zero, coeff_X_zero, sub_zero, one_ne_zero] at this
  · exact this
  · exact greatestFactorOneSubNotDvd_ne_zero p hp

end greatestFactorOneSubNotDvd

/--
A polynomial which makes it easier to define the Hilbert polynomial. Look at the theorem
`Polynomial.preHilbert_eq_choose_sub_add`, which states that for any `d k n : ℕ` with `k ≤ n`,
`(Polynomial.preHilbert d k).eval (n : ℚ) = Nat.choose (n - k + d) d`.
-/
noncomputable def preHilbert (d k : ℕ) : ℚ[X] :=
  (d.factorial : ℚ)⁻¹ • (∏ i : Finset.range d, (X - (C (k : ℚ)) + (C (i : ℚ)) + 1))

local notation "gFOSND" => greatestFactorOneSubNotDvd

theorem preHilbert_eq_choose_sub_add (d k n : ℕ) (hkn : k ≤ n):
    (preHilbert d k).eval (n : ℚ) = Nat.choose (n - k + d) d := by
  rw [preHilbert]
  simp only [Finset.univ_eq_attach, map_natCast, eval_smul, eval_prod, eval_add, eval_sub, eval_X,
    eval_natCast, eval_one, smul_eq_mul]
  rw [inv_mul_eq_iff_eq_mul₀]
  pick_goal 2
  · exact_mod_cast d.factorial_ne_zero
  norm_cast
  rw [Finset.prod_attach (s := Finset.range d) (f := fun i => (n - k + i + 1)),
    mul_comm, show ∏ x ∈ Finset.range d, (n - k + x + 1) = ∏ x ∈ Finset.range d, ((n - k + 1) + x)
      from Finset.prod_congr rfl fun _ _ => by omega, ← Nat.ascFactorial_eq_prod_range]
  refine Nat.mul_right_inj (n - k).factorial_ne_zero |>.1 ?_
  rw [Nat.factorial_mul_ascFactorial (n - k) d,
    show (n - k).factorial * ((n - k + d).choose d * d.factorial) =
      (n - k + d).choose d * d.factorial * (n - k).factorial by group,
    show (n - k).factorial = (n - k + d - d).factorial by congr 1; omega,
    Nat.choose_mul_factorial_mul_factorial]
  omega

/--
Given `p : ℤ[X]` and `d : ℕ`, the Hilbert polynomial of `p` and `d`.
Look at `Polynomial.coeff_mul_invOneSubPow_eq_hilbert_eval`, which says
that `PowerSeries.coeff ℤ n (p * invOneSubPow ℤ d)` is equal to
`(Polynomial.hilbert p d).eval (n : ℚ)` for any large enough `n : ℕ`.
-/
noncomputable def hilbert (p : ℤ[X]) (d : ℕ) : ℚ[X] :=
  if h : p = 0 then 0
  else if d ≤ p.rootMultiplicity 1 then 0
  else ∑ i ∈ Finset.range ((greatestFactorOneSubNotDvd p h).natDegree + 1),
  ((greatestFactorOneSubNotDvd p h).coeff i) • preHilbert (d - p.rootMultiplicity 1 - 1) i

/--
Given `p : ℤ[X]` and `d : ℕ`. The key property of the Hilbert polynomial with respect to
`p` and `d`, which says that for any term of `p * invOneSubPow ℤ d` whose degree is
large enough, its coefficient can be obtained by evaluating the Hilbert polynomial.
-/
theorem coeff_mul_invOneSubPow_eq_hilbert_eval (p : ℤ[X]) (d n : ℕ) (hn : p.natDegree < n) :
    PowerSeries.coeff ℤ n (p * invOneSubPow ℤ d) = (hilbert p d).eval (n : ℚ) := by
  rw [hilbert]; by_cases h : p = 0
  · simp only [h, coe_zero, zero_mul, map_zero, Int.cast_zero, ↓reduceDIte, eval_zero]
  · simp only [h, reduceDIte, zsmul_eq_mul]
    have coe_one_sub : (1 - X : ℤ[X]).toPowerSeries = 1 - (PowerSeries.X : ℤ⟦X⟧) :=
      PowerSeries.ext_iff.2 fun i => by_cases (fun (hi : i = 0) => by
      simp only [hi, coeff_coe, coeff_sub, coeff_one_zero, coeff_X_zero, sub_zero,
      map_sub, PowerSeries.coeff_one, ↓reduceIte, coeff_zero_X]) (fun hi => by
      simp only [coeff_coe, coeff_sub, map_sub, PowerSeries.coeff_one, hi, reduceIte,
      zero_sub]; rw [Polynomial.coeff_one]; simp only [hi, ↓reduceIte, zero_sub, neg_inj];
      rw [Polynomial.coeff_X, PowerSeries.coeff_X]; exact by_cases (fun (hi : i = 1) => by
      simp only [hi]) (fun hi => by simp only [hi]; exact if_neg <| Ne.symm hi))
    by_cases h1 : d ≤ p.rootMultiplicity 1
    · simp only [h1, reduceIte, eval_zero, Int.cast_eq_zero]
      rw [← pow_rootMultiplicity_mul_greatestFactorOneSubNotDvd_eq p h, mul_comm, coe_mul,
        ← mul_assoc, coe_pow, coe_one_sub, ← @Nat.sub_add_cancel (p.rootMultiplicity 1) d h1,
        mul_comm (invOneSubPow ℤ d).val, pow_add, mul_assoc ((1 - PowerSeries.X) ^
        (p.rootMultiplicity 1 - d)), ← invOneSubPow_inv_eq_one_sub_pow ℤ d, Units.inv_eq_val_inv,
        Units.inv_mul, mul_one, ← coe_one_sub, ← coe_pow, ← coe_mul, coeff_coe]
      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt
        (natDegree_pow_rootMultiplicity_sub_mul_greatestFactorOneSubNotDvd_le p h d h1) hn)
    · simp only [h1, reduceIte]
      rw [coe_inj.2 (pow_rootMultiplicity_mul_greatestFactorOneSubNotDvd_eq p h).symm, coe_mul,
        mul_comm ((1 - X : ℤ[X]) ^ p.rootMultiplicity 1).toPowerSeries, mul_assoc,
        show d = p.rootMultiplicity 1 + (d - p.rootMultiplicity 1) by rw [Nat.add_sub_of_le <|
        Nat.le_of_not_ge h1], invOneSubPow_add, Units.val_mul, ← mul_assoc ((1 - X : ℤ[X]) ^
        rootMultiplicity 1 p).toPowerSeries, coe_pow, coe_one_sub,
        ← invOneSubPow_inv_eq_one_sub_pow, Units.inv_eq_val_inv, Units.inv_mul, one_mul,
        add_tsub_cancel_left]
      rw [show (gFOSND p h).toPowerSeries = (Finset.sum (Finset.range ((gFOSND p h).natDegree + 1))
        (fun (i : ℕ) => ((gFOSND p h).coeff i) • (X ^ i)) : ℤ[X]).toPowerSeries by
        simp only [zsmul_eq_mul, coe_inj]; exact as_sum_range_C_mul_X_pow (gFOSND p h)]
      simp only [zsmul_eq_mul, eval_finset_sum, eval_mul, eval_intCast]
      rw [(Finset.sum_eq_sum_iff_of_le (fun i hi => by
        simp only [Subtype.forall, Finset.mem_range] at *; rw [preHilbert_eq_choose_sub_add
        (d - p.rootMultiplicity 1 - 1) i n <| Nat.le_trans (Nat.le_of_lt_succ hi) (le_trans
        (natDegree_greatestFactorOneSubNotDvd_le p h) (le_of_lt hn))])).2 <| fun i hi => by
        simp only [Subtype.forall, Finset.mem_range, mul_eq_mul_left_iff, Int.cast_eq_zero] at *;
        exact Or.intro_left _ <| preHilbert_eq_choose_sub_add (d - p.rootMultiplicity 1 - 1) i n <|
        Nat.le_trans (Nat.le_of_lt_succ hi) (le_trans (natDegree_greatestFactorOneSubNotDvd_le p h)
        (le_of_lt hn)), PowerSeries.coeff_mul]
      simp only [coeff_coe, finset_sum_coeff, coeff_intCast_mul, Int.cast_id, coeff_X_pow, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range, coeff_mk, ite_mul, zero_mul,
        Int.cast_sum, Int.cast_ite, Int.cast_mul, Int.cast_ofNat, Int.cast_zero]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        show n.succ = (gFOSND p h).natDegree + 1 + (n.succ - ((gFOSND p h).natDegree + 1)) by
        simp only [Nat.succ_sub_succ_eq_sub]; rw [add_assoc, add_comm, add_assoc,
        Nat.sub_add_cancel (le_trans (natDegree_greatestFactorOneSubNotDvd_le p h) (le_of_lt hn))];
        exact n.succ_eq_one_add, Finset.sum_range_add]
      simp only [Nat.succ_sub_succ_eq_sub, add_lt_iff_neg_left, not_lt_zero', reduceIte,
        Finset.sum_const_zero, add_zero]
      rw [invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℤ (d - rootMultiplicity 1 p)
        (tsub_pos_iff_not_le.mpr h1)]
      refine (Finset.sum_eq_sum_iff_of_le (fun i hi => ?_)).2 <| fun i hi => ?_ <;>
      simp only [Finset.mem_range, invOneSubPow] at hi <;>
      simp only [hi, ↓reduceIte, invOneSubPow, coeff_mk, Int.cast_natCast]
      rw [add_comm]
      congr 2
      rw [add_comm]

/--
The Hilbert polynomial is unique. In other words, for any `h : ℚ[X]`, if `h`
satisfies the key property of the Hilbert polynomial (i.e. for any large enough
`n : ℕ`, `PowerSeries.coeff ℤ n (p * (@invOneSubPow ℤ _ d)) = h.eval (n : ℚ)`),
then `h` is the Hilbert polynomial.
-/
theorem exists_unique_hilbert (p : Polynomial ℤ) (d : ℕ) :
    ∃! (h : ℚ[X]), (∃ (N : ℕ), (∀ (n : ℕ) (_ : N < n),
    PowerSeries.coeff ℤ n (p * invOneSubPow ℤ d) = h.eval (n : ℚ))) :=
  ⟨hilbert p d, ⟨p.natDegree, fun n hn => coeff_mul_invOneSubPow_eq_hilbert_eval p d n hn⟩,
  fun q ⟨N, hqN⟩ => eq_of_infinite_eval_eq q (hilbert p d) <| fun hfin => Set.Infinite.image
  (Set.injOn_of_injective $ Nat.cast_injective) (Set.Ioi_infinite (max N p.natDegree)) <|
  Set.Finite.subset hfin <| show @Nat.cast ℚ _ '' (Set.Ioi (max N p.natDegree)) ⊆
  (@setOf ℚ fun x => q.eval x = (hilbert p d).eval x) by
  intro x hx; simp only [Set.mem_image, Set.mem_Ioi, max_lt_iff, Set.mem_setOf_eq] at hx ⊢;
  rcases hx with ⟨n, ⟨h1, h2⟩, h3⟩; rw [← h3, ← coeff_mul_invOneSubPow_eq_hilbert_eval p d n h2];
  exact (Rat.ext (congrArg Rat.num (hqN n h1)) (congrArg Rat.den (hqN n h1))).symm⟩

lemma prod_sub_rootMultiplicity_coeff_eq_one (p : ℤ[X]) (d x : ℕ) :
    coeff (∏ x1 ∈ Finset.attach (Finset.range (d - p.rootMultiplicity 1 - 1)),
    (X - (x : ℚ[X]) + ↑↑x1 + 1)) (d - p.rootMultiplicity 1 - 1) = 1 := by
  let hcoeff := @coeff_prod_of_natDegree_le ℚ ({ x // x ∈ Finset.range
    (d - p.rootMultiplicity 1 - 1) }) (Finset.attach (Finset.range (d - p.rootMultiplicity 1 - 1)))
    _ (fun x1 => X - (x : ℚ[X]) + ↑↑x1 + 1) 1 <| show ∀ x1 ∈ Finset.attach
    (Finset.range (d - p.rootMultiplicity 1 - 1)), natDegree (X - (x : ℚ[X]) + ↑↑x1 + 1) ≤ 1 by
    intro x1 _; exact le_trans (natDegree_add_le _ _) <| by
      simp only [natDegree_one, ge_iff_le, zero_le, max_eq_left];
      exact le_trans (natDegree_add_le _ _) <| by
        simp only [natDegree_natCast, ge_iff_le, zero_le, max_eq_left];
        exact le_trans (natDegree_sub_le _ _) <| by
          simp only [natDegree_X, natDegree_natCast, ge_iff_le, zero_le, max_eq_left, le_refl]
  simp only [Finset.card_attach, Finset.card_range, mul_one, coeff_add, coeff_sub, coeff_X_one,
    coeff_natCast_ite, one_ne_zero, ↓reduceIte, CharP.cast_eq_zero, sub_zero, add_zero,
    Finset.prod_const] at hcoeff
  rw [hcoeff, Polynomial.coeff_one]; simp only [one_ne_zero, ↓reduceIte, add_zero, one_pow]

/--
This theorem tells us the specific degree of any non-zero Hilbert polynomial.
-/
theorem natDegree_hilbert (p : ℤ[X]) (d : ℕ) (hh : hilbert p d ≠ 0) :
    (hilbert p d).natDegree = d - p.rootMultiplicity 1 - 1 := by
  by_cases h : p = 0
  · exfalso; rw [hilbert] at hh; simp only [h, ↓reduceDIte, ne_eq, not_true_eq_false] at hh
  · by_cases h1 : d ≤ p.rootMultiplicity 1
    · rw [hilbert] at hh
      simp only [h1, ↓reduceIte, dite_eq_ite, ite_self, ne_eq, not_true_eq_false] at hh
    · refine' natDegree_eq_of_le_of_coeff_ne_zero _ _
      · rw [hilbert]; simp only [h, ↓reduceDIte, h1, ↓reduceIte, zsmul_eq_mul]
        refine' @natDegree_sum_le_of_forall_le ℕ (Finset.range (natDegree (gFOSND p h) + 1)) ℚ _
          (d - p.rootMultiplicity 1 - 1) (fun x => (@Int.cast ℚ[X] _ ((gFOSND p h).coeff x)) *
          preHilbert (d - p.rootMultiplicity 1 - 1) x) _
        · intro i _
          refine' le_trans (@natDegree_mul_le ℚ _ (@Int.cast ℚ[X] _ (coeff (gFOSND p h) i))
            (preHilbert (d - p.rootMultiplicity 1 - 1) i)) _
          · simp only [natDegree_intCast, zero_add]; rw [preHilbert]
            refine' le_trans (natDegree_smul_le (@Inv.inv ℚ _
              (d - p.rootMultiplicity 1 - 1).factorial) _) _
            · refine' le_trans (natDegree_prod_le (@Finset.attach ℕ (Finset.range
                (d - p.rootMultiplicity 1 - 1))) _) _
              · have : ∀ x ∈ Finset.attach (Finset.range (d - p.rootMultiplicity 1 - 1)),
                    natDegree (X - (i : ℚ[X]) + ↑↑x + 1) ≤ 1 :=
                  fun x _ => le_trans (natDegree_add_le _ _) <| by
                  simp only [natDegree_one, ge_iff_le, zero_le, max_eq_left];
                  exact le_trans (natDegree_add_le _ _) <| by
                    simp only [natDegree_natCast, ge_iff_le, zero_le, max_eq_left];
                    exact le_trans (natDegree_sub_le _ _) <| by simp only [natDegree_X,
                      natDegree_natCast, ge_iff_le, zero_le, max_eq_left, le_refl]
                exact le_trans (Finset.sum_le_sum this) <| by simp only [Finset.sum_const,
                  Finset.card_attach, Finset.card_range, smul_eq_mul, mul_one, le_refl]
      · rw [hilbert]
        simp only [h, ↓reduceDIte, h1, ↓reduceIte, zsmul_eq_mul, finset_sum_coeff,
          coeff_intCast_mul, ne_eq]
        simp_rw [preHilbert, coeff_smul]
        simp only [Finset.univ_eq_attach, map_natCast, smul_eq_mul]
        simp_rw [prod_sub_rootMultiplicity_coeff_eq_one p]; rw [← Finset.sum_mul]
        simp only [mul_one, mul_eq_zero, _root_.inv_eq_zero, Nat.cast_eq_zero]; rw [not_or]
        constructor
        · rw [show ∑ i ∈ Finset.range ((gFOSND p h).natDegree + 1), @Int.cast ℚ _
            ((gFOSND p h).coeff i) = (gFOSND p h).eval 1 by rw [eval_eq_sum_range]; simp only
            [one_pow, mul_one, Int.cast_sum]]
          intro h'; simp only [Int.cast_eq_zero] at h'; rw [greatestFactorOneSubNotDvd] at h'
          simp only [map_one, eval_mul, eval_pow, eval_neg, eval_one, Int.reduceNeg, mul_eq_zero,
            pow_eq_zero_iff', neg_eq_zero, one_ne_zero, ne_eq, rootMultiplicity_eq_zero_iff,
            IsRoot.def, not_forall, exists_prop, false_and, false_or] at h'
          let this := (exists_eq_pow_rootMultiplicity_mul_and_not_dvd p h 1).choose_spec.2
          rw [dvd_iff_isRoot] at this; exact this h'
        · exact Nat.factorial_ne_zero _

end Polynomial
