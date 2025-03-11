/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import DimensionTheory.IntegerValuedPolynomial

/-!
# Polyomial like functions

A function `f : ℤ → ℤ` is called polynomial-like function if there is a polynomial `p : ℚ[X]` such
that `f(n) = p(n)` for sufficiently large `n`.
-/

open Polynomial Filter List Function

variable {R : Type*} [Ring R]

/--
A function `ℤ → ℤ` is polynomial like if `f(n) = p(n)` for some polynomial `p : ℚ[X]` and all large
enough `n : ℤ`
-/
class Function.PolynomialLike (f : R → ℤ) : Prop where
  out : ∃ (p : ℚ[X]), ∀ᶠ (n : ℤ) in atTop, f n = (p.eval n : ℚ)

instance : Function.PolynomialLike (0 : R → ℤ) where
  out := ⟨0, by simp⟩

/--
If `f` is a polynomial-like function, then `f.polynomial` is the polynomial representing `f`.
-/
noncomputable abbrev Function.polynomial (f : R → ℤ) [hf : f.PolynomialLike] : ℚ[X] :=
  hf.out.choose

lemma Function.polynomial_spec (f : R → ℤ) [hf : f.PolynomialLike] :
    ∀ᶠ (n : ℤ) in atTop, (f n : ℚ) = (f.polynomial.eval n : ℚ) :=
  hf.out.choose_spec

lemma Function.polynomial_uniq (f : R → ℤ) [f.PolynomialLike]
    {p : ℚ[X]} (hp : ∀ᶠ (n : ℤ) in atTop, (f n : ℚ) = (p.eval n : ℚ)) :
    p = f.polynomial := by
  have hf' := f.polynomial_spec
  simp only [eventually_atTop, ge_iff_le] at hf' hp
  obtain ⟨n, hn⟩ := hf'
  obtain ⟨m, hm⟩ := hp

  apply eq_of_infinite_eval_eq
  fapply Set.Infinite.mono (s := Set.image (↑) $ Set.Ici (max m n))
  · rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_Ici, max_le_iff] at hx
    specialize hm x (by omega)
    specialize hn x (by omega)
    simp [← hm, ← hn]
  · refine Set.Infinite.image ?_ (Set.Ici_infinite _)
    intro _ _ _ _ h
    exact_mod_cast h

lemma Function.polynomial_zero : (0 : R → ℤ).polynomial = 0 := by
  symm
  apply polynomial_uniq
  simp

instance Function.polynomial_isIntegerValued (f : R → ℤ) [f.PolynomialLike] :
    f.polynomial.IsIntegerValued := by
  rw [isIntegerValued_def']
  have hf := f.polynomial_spec
  simp only [eventually_atTop, ge_iff_le] at hf
  obtain ⟨n, hn⟩ := hf
  refine ⟨n, fun m hm => ?_⟩
  rw [← hn m hm]
  exact ⟨f m, rfl⟩

instance (f : R → ℤ) [f.PolynomialLike] :
    (Δᶠ f).PolynomialLike := by
  have hf' := f.polynomial_spec
  refine ⟨Δᵖ f.polynomial, ?_⟩
  simp only [eventually_atTop, ge_iff_le, stdDiff.eval_eq] at hf' ⊢
  obtain ⟨n, hn⟩ := hf'
  exact ⟨n, fun m hm => by
    rw [stdDiffFunc, Int.cast_sub]
    have := hn (m + 1) (by omega)
    simp only [Int.cast_add, Int.cast_one] at this
    rw [this, hn m hm]⟩

instance iter_diff_polynomialLike (f : R → ℤ) [f.PolynomialLike] (n : ℕ) :
    (Δᶠ^[n] f).PolynomialLike := by
  induction n with
  | zero => simpa
  | succ n ih =>
    simp only [iterate_succ', comp_apply]
    infer_instance

lemma Function.stdDiff_polynomial_eq (f : R → ℤ) [f.PolynomialLike] :
    (Δᶠ f).polynomial = Δᵖ f.polynomial := by
  symm
  apply polynomial_uniq
  have hf := f.polynomial_spec
  simp only [eventually_atTop, ge_iff_le, stdDiff.eval_eq] at hf ⊢
  exact hf.imp fun m h n hmn => by
    rw [stdDiffFunc, Int.cast_sub]
    have := h (n + 1) (by omega)
    simp only [Int.cast_add, Int.cast_one] at this
    rw [this, h n hmn]

lemma Function.stdDiff_pow_polynomial_eq (f : R → ℤ) [f.PolynomialLike] (m : ℕ) :
    (Δᶠ^[m] f).polynomial = Δᵖ^[m] f.polynomial := by
  induction m with
  | zero => simp
  | succ n ih =>
    simp only [iterate_succ', comp_apply, f.stdDiff_polynomial_eq, ← ih]
    apply stdDiff_polynomial_eq

lemma Function.stdDiff_eventually_eq_zero
    (f : R → ℤ) [f.PolynomialLike] :
    ∃ (r : ℕ), ∀ᶠ (n : ℤ) in atTop, (Δᶠ^[r] f) n = 0 := by
  have h := stdDiff.eventually_eq_zero f.polynomial
  simp only [eventually_atTop, ge_iff_le] at h ⊢
  obtain ⟨r, hr⟩ := h
  refine ⟨r, ?_⟩
  have h := (Δᶠ^[r] f).polynomial_spec
  simp only [eventually_atTop, ge_iff_le] at h
  obtain ⟨m, hm⟩ := h
  refine ⟨max m r, fun a ha => ?_⟩
  apply_fun ((↑) : ℤ → ℚ) using Int.cast_injective
  rw [hm a (by omega)]
  specialize hr r (le_refl _)
  rw [← stdDiff_pow_polynomial_eq] at hr
  rw [hr, eval_zero, Int.cast_zero]

instance (f : R → ℤ) [(Δᶠ f).PolynomialLike] : f.PolynomialLike := by
  let P := (Δᶠ  f).polynomial
  let R := ∫ᵖ P
  have hR : R.IsIntegerValued := (polynomial_isIntegerValued _).antideriv
  let g : ℤ → ℤ := fun n => f n - R.evalInt n
  have hg : ∀ᶠ (n : ℤ) in atTop, (Δᶠ g) n = 0 := by
    have hf := (Δᶠ f).polynomial_spec
    simp only [eventually_atTop, ge_iff_le] at hf ⊢
    obtain ⟨n, hn⟩ := hf
    refine ⟨n, fun m hm => ?_⟩
    specialize hn m hm
    simp only [stdDiffFunc, Int.cast_add, Int.cast_one, g]
    rw [show f (m + 1) - R.evalInt (m + 1) - (f m - R.evalInt m) =
      (f (m + 1) - f m) - (R.evalInt (m + 1) - R.evalInt m) by abel,
      show f (m + 1) - f m = Δᶠ f m from rfl,
      show R.evalInt (m + 1) - R.evalInt m = (Δᵖ R).evalInt m by
        apply_fun ((↑) : ℤ → ℚ) using Int.cast_injective
        simp [evalInt_spec]]
    apply_fun ((↑) : ℤ → ℚ) using Int.cast_injective
    rw [Int.cast_sub, hn, evalInt_spec,
      show stdDiff R = P from binomialPolynomial.stdDiff_antideriv _, Int.cast_zero, sub_eq_zero]

  obtain ⟨e, hg⟩ : ∃ e, ∀ᶠ (n : ℤ) in atTop, g n = e :=
    stdDiffFunc.eventually_constant_of_stdDiffFunc_eventually_eq_zero_int _ hg

  have h : ∀ᶠ (n : ℤ) in atTop, f n = R.evalInt n + e := by
    simp only [eventually_atTop, ge_iff_le] at hg ⊢
    obtain ⟨n, hn⟩ := hg
    refine ⟨n, fun m hm => ?_⟩
    specialize hn m hm
    simp only [g] at hn
    rw [← hn]
    abel

  refine ⟨R + C (e : ℚ), ?_⟩
  simp only [eventually_atTop, ge_iff_le, map_intCast, eval_add, eval_intCast] at h ⊢
  obtain ⟨n, hn⟩ := h
  refine ⟨n, fun m hm => ?_⟩
  specialize hn m hm
  simp [hn, evalInt_spec]


lemma Function.PolynomialLike.of_stdDiffFunc_pow
    (f : R → ℤ) (k : ℕ) [h : (Δᶠ^[k] f).PolynomialLike] : f.PolynomialLike := by
  induction k generalizing h with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply] at h
    have : PolynomialLike (Δᶠ^[k] f) := iter_diff_polynomialLike f _
    apply ih

lemma Function.PolynomialLike.of_stdDiffFunc_pow_eventually_zero
    (f : R → ℤ) (hf : ∃ (r : ℕ), ∀ᶠ (n : ℤ) in atTop, (Δᶠ^[r] f) n = 0) :
    f.PolynomialLike := by
  obtain ⟨r, hr⟩ := hf
  haveI : (Δᶠ^[r] f).PolynomialLike := by
    refine ⟨0, ?_⟩
    simp only [eventually_atTop, ge_iff_le, eval_zero, Int.cast_eq_zero] at hr ⊢
    obtain ⟨n, hn⟩ := hr
    refine ⟨n, fun m hm => ?_⟩
    exact hn m hm
  exact of_stdDiffFunc_pow _ r


/--
Serre's local algebra

Chapter II.B.2 Lemma 2 page 21.
-/
lemma Function.PolynomialLike.tfae (f : ℤ → ℤ) : TFAE
    [
      f.PolynomialLike,
      (Δᶠ f).PolynomialLike,
      ∃ (r : ℕ), ∀ᶠ (n : ℤ) in atTop, (Δᶠ^[r] f) n = 0
    ] := by
  tfae_have 1 → 2 := by
    intro _; infer_instance

  tfae_have 1 → 3 := by
    intro hf; apply stdDiff_eventually_eq_zero

  tfae_have 2 → 1 := by
    intro _; infer_instance

  tfae_have 3 → 1 := by
    apply of_stdDiffFunc_pow_eventually_zero

  tfae_finish
