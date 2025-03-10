/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Group

import DimensionTheory.missing_lemmas.Int


/-!
# Some missing lemmas on factorial
-/

open BigOperators Nat

theorem Nat.right_factorial_dvd_ascFactorial (n k : ℕ) :
    k ! ∣ n.ascFactorial k := by
  rw [ascFactorial_eq_factorial_mul_choose']
  simp

open Asymptotics Nat Filter

theorem Nat.choose_isEquivalent (k : ℕ) :
    (fun (n : ℕ) => (n.choose k : ℚ)) ~[atTop]
    (fun (n : ℕ) => (n ^ k / k ! : ℚ)) := by
  rw [isEquivalent_iff_exists_eq_mul]
  refine ⟨fun n => ∏ i ∈ Finset.range k, ((n - i) / n : ℚ), ?_, ?_⟩

  · rw [show (1 : ℚ) = ∏ i ∈ Finset.range k, 1 by simp]
    apply tendsto_finset_prod
    intro i _
    change Tendsto ((fun b : ℕ => (b - i : ℚ)) / (fun b : ℕ => (b : ℚ))) _ _
    rw [← isEquivalent_iff_tendsto_one]
    change  (((↑) : ℕ → ℚ) - Function.const ℕ (i : ℚ)) ~[atTop] ((↑) : ℕ → ℚ)
    apply IsEquivalent.sub_isLittleO
    · rfl
    · rw [isLittleO_iff]
      simp only [Function.const_apply, eventually_atTop, ge_iff_le]
      intro c hc
      obtain ⟨m, hm⟩ := exists_nat_gt (i / c)
      refine ⟨m, fun k hk => ?_⟩
      simp only [norm, Rat.cast_natCast, abs_cast]
      rw [div_lt_iff₀ (hc := hc), mul_comm] at hm
      apply_fun ((↑) : ℕ → ℝ) at hk using mono_cast (α := ℝ)
      refine le_of_lt $ lt_of_lt_of_le hm ?_
      apply mul_le_mul (le_refl (c : ℝ)) hk <;> norm_cast <;> linarith

    · simp only [ne_eq, eventually_atTop, ge_iff_le]
      refine ⟨i + 1, fun n hn h => ?_⟩
      simp only [cast_eq_zero] at h
      subst h
      omega

  · change ∀ᶠ _ in _, _
    simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range, Pi.mul_apply,
      eventually_atTop, ge_iff_le]
    refine ⟨k + 1, fun m hm => ?_⟩
    rw [div_mul_eq_mul_div]
    symm
    rw [div_eq_iff]
    pick_goal 2
    · intro r
      simp only [pow_eq_zero_iff', cast_eq_zero, ne_eq] at r
      omega
    rw [← mul_div_assoc]
    rw [div_eq_iff]
    pick_goal 2
    · simp only [ne_eq, cast_eq_zero]
      exact factorial_ne_zero k
    suffices eq : (∏ x ∈ Finset.range k, (m - x)) * m ^ k = ((m.choose k) * m ^ k * k !) by
      apply_fun ((↑) : ℕ → ℚ) at eq
      simp only [cast_mul, cast_pow, cast_prod] at eq
      rw [← eq]
      congr 1
      refine Finset.prod_congr rfl fun x hx => ?_
      simp only [Finset.mem_range] at hx
      rw [Nat.cast_sub]
      omega
    rw [show m.choose k * m ^ k * k ! = (k ! * m.choose k) * m ^ k by group,
      ← Nat.descFactorial_eq_factorial_mul_choose m k, descFactorial_eq_prod_range]

theorem Nat.choose_isEquivalent_atTop_int (k : ℕ) :
    (fun (n : ℤ) => (n.toNat.choose k : ℚ)) ~[atTop]
    (fun (n : ℤ) => (n ^ k / k ! : ℚ)) := by
  have h1 := Nat.choose_isEquivalent k

  rw [isEquivalent_iff_tendsto_one] at h1 ⊢

  pick_goal 2
  · simp only [ne_eq, div_eq_zero_iff, pow_eq_zero_iff', Int.cast_eq_zero, cast_eq_zero, not_or,
    not_and, Decidable.not_not, eventually_atTop, ge_iff_le]
    exact ⟨1, fun n hn => ⟨by omega, factorial_ne_zero k⟩⟩

  pick_goal 2
  · simp only [ne_eq, div_eq_zero_iff, pow_eq_zero_iff', cast_eq_zero, not_or, not_and,
    Decidable.not_not, eventually_atTop, ge_iff_le]
    exact ⟨1, fun n hn => ⟨by omega, factorial_ne_zero k⟩⟩
  -- rw [← @Int.comap_cast_atTop ℚ _ _]

  rw [tendsto_iff_forall_eventually_mem] at h1 ⊢
  intro s hs
  specialize h1 s hs
  simp only [Pi.div_apply, eventually_atTop, ge_iff_le] at h1 ⊢
  obtain ⟨N, hN⟩ := h1
  refine ⟨N, fun m hm => ?_⟩
  specialize hN m.toNat (by rwa [Int.le_toNat]; linarith)
  convert hN
  symm

  have := Int.coe_toNat_of_nonneg (m : ℤ) (by linarith)
  apply_fun ((↑): ℤ → ℚ) at this
  exact this
