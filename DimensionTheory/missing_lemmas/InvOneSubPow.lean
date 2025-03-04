/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.PowerSeries.Basic

namespace PowerSeries

variable (S : Type*) [CommRing S] (d : ℕ)

/--
(1 + X + X^2 + ...) * (1 - X) = 1.

Note that the power series `1 + X + X^2 + ...` is written as `mk 1` where `1` is the constant
function so that `mk 1` is the power series with all coefficients equal to one.
-/
theorem mk_one_mul_one_sub_eq_one : (mk 1 : S⟦X⟧) * (1 - X) = 1 := by
  rw [mul_comm, PowerSeries.ext_iff]
  intro n
  cases n with
  | zero => simp
  | succ n => simp [sub_mul]

/--
Note that `mk 1` is the constant function `1` so the power series `1 + X + X^2 + ...`. This theorem
states that for any `d : ℕ`, `(1 + X + X^2 + ... : S⟦X⟧) ^ (d + 1)` is equal to the power series
`mk fun n => Nat.choose (d + n) d : S⟦X⟧`.
-/
theorem mk_one_pow_eq_mk_choose_add :
    (mk 1 : S⟦X⟧) ^ (d + 1) = (mk fun n => Nat.choose (d + n) d : S⟦X⟧) := by
  induction d with
  | zero => ext; simp
  | succ d hd =>
      ext n
      rw [pow_add, hd, pow_one, mul_comm, coeff_mul]
      simp_rw [coeff_mk, Pi.one_apply, one_mul]
      norm_cast
      rw [Finset.sum_antidiagonal_choose_add, ← Nat.choose_succ_succ, Nat.succ_eq_add_one,
        add_right_comm]

/--
Given a natural number `d : ℕ` and a commutative ring `S`, `PowerSeries.invOneSubPow S d` is the
multiplicative inverse of `(1 - X) ^ d` in `S⟦X⟧ˣ`. When `d` is `0`, `PowerSeries.invOneSubPow S d`
will just be `1`. When `d` is positive, `PowerSeries.invOneSubPow S d` will be the power series
`mk fun n => Nat.choose (d - 1 + n) (d - 1)`.
-/
noncomputable def invOneSubPow : ℕ → S⟦X⟧ˣ
  | 0 => 1
  | d + 1 => {
    val := mk fun n => Nat.choose (d + n) d
    inv := (1 - X) ^ (d + 1)
    val_inv := by
      rw [← mk_one_pow_eq_mk_choose_add, ← mul_pow, mk_one_mul_one_sub_eq_one, one_pow]
    inv_val := by
      rw [← mk_one_pow_eq_mk_choose_add, ← mul_pow, mul_comm, mk_one_mul_one_sub_eq_one, one_pow]
    }

theorem invOneSubPow_zero : invOneSubPow S 0 = 1 := by
  delta invOneSubPow
  simp only [Units.val_one]

theorem invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos (h : 0 < d) :
    (invOneSubPow S d).val = (mk fun n => Nat.choose (d - 1 + n) (d - 1) : S⟦X⟧) := by
  rw [← Nat.sub_one_add_one_eq_of_pos h, invOneSubPow, add_tsub_cancel_right]

theorem invOneSubPow_val_succ_eq_mk_add_choose :
    (invOneSubPow S (d + 1)).val = (mk fun n => Nat.choose (d + n) d : S⟦X⟧) := rfl

/--
The theorem `PowerSeries.mk_one_mul_one_sub_eq_one` implies that `1 - X` is a unit in `S⟦X⟧`
whose inverse is the power series `1 + X + X^2 + ...`. This theorem states that for any `d : ℕ`,
`PowerSeries.invOneSubPow S d` is equal to `(1 - X)⁻¹ ^ d`.
-/
theorem invOneSubPow_eq_inv_one_sub_pow :
    invOneSubPow S d =
      (Units.mkOfMulEqOne (1 - X) (mk 1 : S⟦X⟧) <|
        Eq.trans (mul_comm _ _) (mk_one_mul_one_sub_eq_one S))⁻¹ ^ d := by
  induction d with
  | zero => exact Eq.symm <| pow_zero _
  | succ d _ =>
      rw [inv_pow]
      exact (DivisionMonoid.inv_eq_of_mul _ (invOneSubPow S (d + 1)) <| by
        rw [← Units.val_eq_one, Units.val_mul, Units.val_pow_eq_pow_val]
        exact (invOneSubPow S (d + 1)).inv_val).symm

theorem invOneSubPow_inv_eq_one_sub_pow :
    (invOneSubPow S d).inv = (1 - X : S⟦X⟧) ^ d := by
  induction d with
  | zero => exact Eq.symm <| pow_zero _
  | succ d => rfl

theorem invOneSubPow_inv_zero_eq_one : (invOneSubPow S 0).inv = 1 := by
  delta invOneSubPow
  simp only [Units.inv_eq_val_inv, inv_one, Units.val_one]

theorem mk_add_choose_mul_one_sub_pow_eq_one :
    (mk fun n ↦ Nat.choose (d + n) d : S⟦X⟧) * ((1 - X) ^ (d + 1)) = 1 :=
  (invOneSubPow S (d + 1)).val_inv

theorem invOneSubPow_add (e : ℕ) :
    invOneSubPow S (d + e) = invOneSubPow S d * invOneSubPow S e := by
  simp_rw [invOneSubPow_eq_inv_one_sub_pow, pow_add]

theorem one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val (e : ℕ) :
    (1 - X) ^ e * (invOneSubPow S (d + e)).val = (invOneSubPow S d).val := by
  simp [invOneSubPow_add, Units.val_mul, mul_comm, mul_assoc, ← invOneSubPow_inv_eq_one_sub_pow]

theorem one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow (e : ℕ) :
    (1 - X) ^ (d + e) * (invOneSubPow S e).val = (1 - X) ^ d := by
  simp [pow_add, mul_assoc, ← invOneSubPow_inv_eq_one_sub_pow S e]

end PowerSeries
