/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/

import DimensionTheory.HilbertSerre.Theorem
import DimensionTheory.RingTheory.HilbertPolynomial

/-!
# Hilbert polynomials

Remember the assumptions in the file `Mathlib/Algebra/HilbertSerre/Theorem.lean`:
`universe u`
`variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]`
`variable [noetherian_ring : IsNoetherianRing A] [finite_module : Module.Finite A M]`
`variable (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]`
`variable (ℳ : ℕ → AddSubgroup M) [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]`
`variable (μ : (FGModuleCat (𝒜 0)) ⟹+ ℤ)`
`variable (S : generatingSetOverBaseRing 𝒜)`

This file inherits all the above settings. With an additional assumption
`hS : ∀ i : S.toFinset, S.deg i.2 = 1`, the main things achieved in this file are:
1. formalising the Hilbert polynomial `HilbertSerre.hilbertPolynomial 𝒜 ℳ μ S : ℚ[X]`;
2. proving that for any large enough `n : ℕ`, the value of the additive function `μ` at `ℳ n`
   is equal to the value of the Hilbert polynomial at `n`;
3. showing that the polynomial `h` satisfying the above property (i.e. for any large enough
   `n : ℕ`, the value of `μ` at `ℳ n` equals the value of `h` at `n`) is unique;
4. proving a theorem `HilbertSerre.natDegree_hilbertPolynomial`, which tells us the specific
   degree of any non-zero Hilbert polynomial.
-/

universe u
variable {A M : Type u}
variable [CommRing A] [noetherian_ring : IsNoetherianRing A]
variable [AddCommGroup M] [Module A M] [finite_module : Module.Finite A M]
variable (𝒜 : ℕ → AddSubgroup A) (ℳ : ℕ → AddSubgroup M)
variable [GradedRing 𝒜] [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
variable (μ : (FGModuleCat (𝒜 0)) ⟹+ ℤ)
variable (S : generatingSetOverBaseRing 𝒜) (hS : ∀ i : S.toFinset, S.deg i.2 = 1)

open BigOperators
open PowerSeries

namespace generatingSetOverBaseRing

omit noetherian_ring in
include hS in
lemma poles_eq_one_sub_pow_of_deg_eq_one :
    S.poles = ⟨1 - X, invOfUnit (1 - X) 1, mul_invOfUnit (1 - X) 1 <| by
    simp only [map_sub, map_one, constantCoeff_X, sub_zero, Units.val_one], by
    rw [mul_comm]; exact mul_invOfUnit (1 - X) 1 <| by simp only [map_sub, map_one,
    constantCoeff_X, sub_zero, Units.val_one]⟩ ^ S.toFinset.card := by
  rw [poles]; simp_rw [hS]; simp only [pow_one, Finset.prod_const, Finset.card_attach]
  exact Units.eq_iff.mp rfl

end generatingSetOverBaseRing

namespace HilbertSerre

open Polynomial
open generatingSetOverBaseRing
open AdditiveFunction

/--
Remember the Hilbert Serre Theorem (`hilbert_serre`), which says that there exists some
`p : ℤ[X]` such that `μ.poincareSeries 𝒜 ℳ = p • S.poles⁻¹`. This definition is the
polynomial `p` guaranteed by `hilbert_serre`.
-/
noncomputable def numeratorPolynomial : Polynomial ℤ := (hilbert_serre 𝒜 ℳ μ S).choose

theorem numeratorPolynomial_mul_inv_poles_eq_poincareSeries :
    (numeratorPolynomial 𝒜 ℳ μ S).toPowerSeries * S.poles⁻¹ = μ.poincareSeries 𝒜 ℳ :=
  (hilbert_serre 𝒜 ℳ μ S).choose_spec.symm

/--
The Hilbert polynomial, i.e. the polynomial such that for any `n : ℕ` which
is big enough, the value of `μ` at `ℳ n` is equal to its value at `n`.
-/
noncomputable def hilbertPolynomial : ℚ[X] :=
  (numeratorPolynomial 𝒜 ℳ μ S).hilbert S.toFinset.card

include hS in
/--
The key property of the Hilbert polynomial, i.e. for any `n : ℕ` that is large enough,
the value of `μ` at `ℳ n` is equal to the value of the Hilbert polynomial at `n`.
-/
theorem AdditiveFunction_eq_hilbertPolynomial_eval
    (n : ℕ) (hn : (numeratorPolynomial 𝒜 ℳ μ S).natDegree < n) :
    (μ (FGModuleCat.of (𝒜 0) (ℳ n)) : ℚ) =
    (hilbertPolynomial 𝒜 ℳ μ S).eval (n : ℚ) := by
  rw [show μ (FGModuleCat.of (𝒜 0) (ℳ n)) = coeff ℤ n (μ.poincareSeries 𝒜 ℳ) by
    rw [poincareSeries, coeff_mk], hilbertPolynomial,
    ← numeratorPolynomial_mul_inv_poles_eq_poincareSeries 𝒜 ℳ μ S,
    poles_eq_one_sub_pow_of_deg_eq_one 𝒜 S hS]
  convert coeff_mul_invOneSubPow_eq_hilbert_eval (numeratorPolynomial 𝒜 ℳ μ S)
    S.toFinset.card n hn using 4
  rw [invOneSubPow_eq_inv_one_sub_pow, inv_pow]
  exact Units.inv_unique rfl

include hS in
/--
The Hilbert polynomial is unique. In other words, for any `h : ℚ[X]`, if `h` satisfies the key
property of the Hilbert polynomial (i.e. for any large enough `n : ℕ`, the value of `μ` at `ℳ n`
equals the value of `h` at `n`), then `h` is the Hilbert polynomial itself.
-/
theorem exists_unique_hilbertPolynomial :
    ∃! (h : ℚ[X]), (∃ (N : ℕ), (∀ (n : ℕ) (_ : N < n),
    (μ (FGModuleCat.of (𝒜 0) (ℳ n)) : ℚ) = h.eval (n : ℚ))) :=
  ⟨hilbertPolynomial 𝒜 ℳ μ S, ⟨(numeratorPolynomial 𝒜 ℳ μ S).natDegree, fun n hn =>
  AdditiveFunction_eq_hilbertPolynomial_eval 𝒜 ℳ μ S hS n hn⟩, fun q ⟨N, hqN⟩ =>
  eq_of_infinite_eval_eq q (hilbertPolynomial 𝒜 ℳ μ S) <| fun hfin => Set.Infinite.image
  (Set.injOn_of_injective Nat.cast_injective) (Set.Ioi_infinite (max N (natDegree
  (numeratorPolynomial 𝒜 ℳ μ S)))) <| Set.Finite.subset hfin <|
  show @Nat.cast ℚ _ '' (Set.Ioi (max N (numeratorPolynomial 𝒜 ℳ μ S).natDegree)) ⊆
  (@setOf ℚ fun x => q.eval x = (hilbertPolynomial 𝒜 ℳ μ S).eval x) by
  intro x hx; simp only [Set.mem_image, Set.mem_Ioi, max_lt_iff, Set.mem_setOf_eq] at hx ⊢;
  rcases hx with ⟨n, ⟨h1, h2⟩, h3⟩; rw [← h3, ← AdditiveFunction_eq_hilbertPolynomial_eval
  𝒜 ℳ μ S hS n h2]; exact (Rat.ext (congrArg _ (hqN n h1)) (congrArg _ (hqN n h1))).symm⟩

/--
This theorem tells us the specific degree of any non-zero Hilbert polynomial.
-/
theorem natDegree_hilbertPolynomial (hhP : hilbertPolynomial 𝒜 ℳ μ S ≠ 0) :
    (hilbertPolynomial 𝒜 ℳ μ S).natDegree =
    S.toFinset.card - (numeratorPolynomial 𝒜 ℳ μ S).rootMultiplicity 1 - 1 :=
  natDegree_hilbert (numeratorPolynomial 𝒜 ℳ μ S) S.toFinset.card hhP

end HilbertSerre
