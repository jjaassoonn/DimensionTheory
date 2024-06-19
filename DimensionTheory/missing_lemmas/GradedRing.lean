/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/

import DimensionTheory.missing_lemmas.GradeZeroMonoid

/-!
# An alternative spelling of the map `A → A₀`
-/

section GradeZero

variable {ι R A σ : Type*}

open SetLike.GradedMonoid DirectSum

variable [Semiring A] [DecidableEq ι]

variable [CanonicallyOrderedAddCommMonoid ι]

variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

/--
The semiring homomorphism from `A` to `𝒜 0` sending every `a : A` to `a₀`.
-/
def GradedRing.projZeroRingHom' : A →+* 𝒜 0 :=
  ((GradedRing.projZeroRingHom 𝒜).codRestrict _ fun _x => SetLike.coe_mem _ :
  A →+* SetLike.GradeZero.subsemiring 𝒜)

@[simp] lemma GradedRing.coe_projZeroRingHom'_apply (a : A) :
    (GradedRing.projZeroRingHom' 𝒜 a : A) = GradedRing.projZeroRingHom 𝒜 a := rfl

@[simp] lemma GradedRing.projZeroRingHom'_apply_coe (a : 𝒜 0) :
    GradedRing.projZeroRingHom' 𝒜 a = a := by
  ext; simp only [coe_projZeroRingHom'_apply, projZeroRingHom_apply, decompose_coe, of_eq_same]

/--
The semiring homomorphism `GradedRing.projZeroRingHom' 𝒜` is surjective.
-/
lemma GradedRing.projZeroRingHom'_surjective :
    Function.Surjective (GradedRing.projZeroRingHom' 𝒜) :=
  Function.RightInverse.surjective (GradedRing.projZeroRingHom'_apply_coe 𝒜)

end GradeZero
