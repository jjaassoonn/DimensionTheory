import DimensionTheory.IntegerValuedPolynomial

open Polynomial Filter List Function


class Function.PolynomialLike (f : ℤ → ℤ) : Prop where
  out : ∃ (p : ℚ[X]), ∀ᶠ (n : ℤ) in atTop, (f n : ℚ) = (p.eval n : ℚ)

instance : Function.PolynomialLike 0 where
  out := ⟨0, by simp⟩

noncomputable abbrev Function.polynomial (f : ℤ → ℤ) [hf : f.PolynomialLike] : ℚ[X] :=
  hf.out.choose

lemma Function.polynomial_spec (f : ℤ → ℤ) [hf : f.PolynomialLike] :
    ∀ᶠ (n : ℤ) in atTop, (f n : ℚ) = (f.polynomial.eval n : ℚ) :=
  hf.out.choose_spec

lemma Function.polynomial_uniq (f : ℤ → ℤ) [f.PolynomialLike]
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

lemma Function.polynomial_zero : (0 : ℤ → ℤ).polynomial = 0 := by
  symm
  apply polynomial_uniq
  simp

instance Function.polynomial_isIntegerValued (f : ℤ → ℤ) [f.PolynomialLike] :
    f.polynomial.IsIntegerValued := by
  rw [isIntegerValued_def']
  have hf := f.polynomial_spec
  simp only [eventually_atTop, ge_iff_le] at hf
  obtain ⟨n, hn⟩ := hf
  refine ⟨n, fun m hm => ?_⟩
  rw [← hn m hm]
  exact ⟨f m, rfl⟩

instance (f : ℤ → ℤ) [f.PolynomialLike] :
    (fΔ f).PolynomialLike := by
  have hf' := f.polynomial_spec
  refine ⟨Δ f.polynomial, ?_⟩
  simp only [eventually_atTop, ge_iff_le, stdDiff.eval_eq] at hf' ⊢
  obtain ⟨n, hn⟩ := hf'
  exact ⟨n, fun m hm => by simp [stdDiffFunc, hn (m + 1) (by omega), hn m hm]⟩

instance (f : ℤ → ℤ) [f.PolynomialLike] (n : ℕ) :
    (fΔ^[n] f).PolynomialLike := by
  induction n with
  | zero => simpa
  | succ n ih =>
    simp only [iterate_succ', comp_apply]
    infer_instance

lemma Function.stdDiff_polynomial_eq (f : ℤ → ℤ) [f.PolynomialLike] :
    (fΔ f).polynomial = Δ f.polynomial := by
  symm
  apply polynomial_uniq
  have hf := f.polynomial_spec
  simp only [eventually_atTop, ge_iff_le, stdDiff.eval_eq] at hf ⊢
  exact hf.imp fun m h n hmn => by simp [stdDiffFunc, h (n + 1) (by omega), h n hmn]

lemma Function.stdDiff_pow_polynomial_eq (f : ℤ → ℤ) [f.PolynomialLike] (m : ℕ) :
    (fΔ^[m] f).polynomial = Δ^[m] f.polynomial := by
  induction m with
  | zero => simp
  | succ n ih =>
    simp only [iterate_succ', comp_apply, f.stdDiff_polynomial_eq, ← ih]
    apply stdDiff_polynomial_eq

lemma Function.stdDiff_eventually_eq_zero
    (f : ℤ → ℤ) [f.PolynomialLike] :
    ∃ (r : ℕ), ∀ᶠ (n : ℤ) in atTop, (fΔ^[r] f) n = 0 := by
  have h := stdDiff.eventually_eq_zero f.polynomial
  simp only [eventually_atTop, ge_iff_le] at h ⊢
  obtain ⟨r, hr⟩ := h
  refine ⟨r, ?_⟩
  have h := (fΔ^[r] f).polynomial_spec
  simp only [eventually_atTop, ge_iff_le] at h
  obtain ⟨m, hm⟩ := h
  refine ⟨max m r, fun a ha => ?_⟩
  apply_fun ((↑) : ℤ → ℚ) using Int.cast_injective
  rw [hm a (by omega)]
  specialize hr r (le_refl _)
  rw [← stdDiff_pow_polynomial_eq] at hr
  rw [hr, eval_zero, Int.cast_zero]

instance (f : ℤ → ℤ) [(fΔ f).PolynomialLike] : f.PolynomialLike := by
  let P := (fΔ  f).polynomial
  have hP : P.IsIntegerValued := polynomial_isIntegerValued _
  let R := ∫ P
  have hR : R.IsIntegerValued := (polynomial_isIntegerValued _).antideriv
  let g : ℤ → ℤ := fun n => f n - R.evalInt n
  have hg : ∀ᶠ (n : ℤ) in atTop, (fΔ g) n = 0 := by
    have hf := (fΔ f).polynomial_spec
    simp only [eventually_atTop, ge_iff_le] at hf ⊢
    obtain ⟨n, hn⟩ := hf
    refine ⟨n, fun m hm => ?_⟩
    specialize hn m hm
    simp only [Int.cast_zero, Int.cast_eq_zero, g, stdDiffFunc]
    rw [show f (m + 1) - R.evalInt (m + 1) - (f m - R.evalInt m) =
      (f (m + 1) - f m) - (R.evalInt (m + 1) - R.evalInt m) by abel,
      show f (m + 1) - f m = fΔ f m from rfl,
      show R.evalInt (m + 1) - R.evalInt m = (Δ R).evalInt m by
        apply_fun ((↑) : ℤ → ℚ) using Int.cast_injective
        simp [evalInt_spec]]
    apply_fun ((↑) : ℤ → ℚ) using Int.cast_injective
    rw [Int.cast_sub, hn, evalInt_spec,
      show stdDiff R = P from binomialPolynomial.stdDiff_antideriv _, Int.cast_zero, sub_eq_zero]

  -- have hg : ∃ e, ∀ᶠ (n : ℤ) in atTop, g n = e := by
  --   refine ⟨g 0, ?_⟩
  --   have hP' := (fΔ f).polynomial_spec
  --   simp only [eventually_atTop, ge_iff_le] at hg hP' ⊢
  --   obtain ⟨n, hn⟩ := hg
  --   obtain ⟨n', hn'⟩ := hP'
  --   refine ⟨max n n', fun m hm => ?_⟩
  --   specialize hn m (by omega)
  --   simp only [stdDiffFunc] at hn
  --   rw [show f (m + 1) - R.evalInt (m + 1) - (f m - R.evalInt m) =
  --     (f (m + 1) - f m) - (R.evalInt (m + 1) - R.evalInt m) by abel,
  --     show f (m + 1) - f m = fΔ f m from rfl,
  --     show R.evalInt (m + 1) - R.evalInt m = (Δ R).evalInt m by
  --       apply_fun ((↑) : ℤ → ℚ) using Int.cast_injective
  --       simp [evalInt_spec]] at hn
  --   simp_rw [show Δ R = P by exact binomialPolynomial.stdDiff_antideriv _] at hn
  --   specialize hn' m (by omega)
  --   rw [← evalInt_spec] at hn'

  -- have h : ∃ e, ∀ᶠ (n : ℤ) in atTop, f n = R.evalInt n + e := by
  --   simp only [eventually_atTop, ge_iff_le] at hg ⊢
  --   obtain ⟨n, hn⟩ := hg
  --   simp? [g, stdDiffFunc] at hn
  sorry

lemma Function.PolynomialLike.tfae (f : ℤ → ℤ) : TFAE
    [
      f.PolynomialLike,
      (fΔ f).PolynomialLike,
      ∃ (r : ℕ), ∀ᶠ (n : ℤ) in atTop, (fΔ^[r] f) n = 0
    ] := by
  tfae_have 1 → 2
  · intro _; infer_instance

  tfae_have 1 → 3
  · intro hf; apply stdDiff_eventually_eq_zero

  sorry
