/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Some missing lemmas about the category of finitely generated modules over a neotherian ring
-/

universe u v

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [Ring R]

namespace FGModuleCat

/-- Interpret a linear map as an arrow in the category of finitely-generated modules.-/
def asHom
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Finite R M] [Module.Finite R N]
    (l : M →ₗ[R] N) :
  FGModuleCat.of R M ⟶ FGModuleCat.of R N :=
  FGModuleCat.ofHom l

section Equivalence

variable {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)

set_option linter.unusedVariables false in
def _root_.RingEquiv.transferFGModule (e : R ≃+* S) (M : Type v) [AddCommGroup M] [Module R M] : Type v := M

instance (M : Type v) [AddCommGroup M] [Module R M] : AddCommGroup (e.transferFGModule M) :=
  inferInstanceAs <| AddCommGroup M

instance (M : Type v) [AddCommGroup M] [Module R M] : Module R (e.transferFGModule M) :=
  inferInstanceAs <| Module R M

instance (M : Type v) [AddCommGroup M] [Module R M] : Module S (e.transferFGModule M) :=
  Module.compHom M e.symm.toRingHom

instance (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.Finite R (e.transferFGModule M) :=
  inferInstanceAs <| Module.Finite R M

instance (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] : Module.Finite S (e.transferFGModule M) := by
  let a : Algebra R S := e.toRingHom.toAlgebra
  have s : IsScalarTower R S (e.transferFGModule M) := by
    constructor
    intros x y z
    convert_to (e.symm (e x * y)) • z = x • (e.symm y • z)
    rw [map_mul, mul_smul, e.symm_apply_apply]

  refine Module.Finite.of_restrictScalars_finite R S _

instance (M : FGModuleCat R) : Module.Finite R M.1 := M.2


/--
For any isomorphic rings `R` and `S`, the category of finitely generated modules over `R` and `S`
are equivalent.
-/
@[simps!]
def _root_.RingEquiv.toFGModuleCatEquivalenceFunctor : FGModuleCat R ⥤ FGModuleCat S :=
{ obj := fun M ↦ .of S (e.transferFGModule M)
  map := fun {X Y} l ↦
    FGModuleCat.ofHom <|
      { toFun := fun x ↦ l x
        map_add' := fun x y ↦ l.hom.map_add x y
        map_smul' := fun r (x : X) ↦ l.hom.map_smul (e.symm r) x }
  map_id := by intros; ext; rfl
  map_comp := by intros; ext; rfl }

/--
For any isomorphic rings `R` and `S`, the category of finitely generated modules over `R` and `S`
are equivalent.
-/
@[simps!]
def _root_.RingEquiv.toFGModuleCatEquivalenceInverse : FGModuleCat S ⥤ FGModuleCat R :=
{ obj := fun M ↦ .of R (e.symm.transferFGModule M)
  map := fun {X Y} l ↦
    FGModuleCat.ofHom <|
    { toFun := fun x ↦ l x
      map_add' := fun x y ↦ l.hom.map_add x y
      map_smul' := fun r (x : X) ↦ l.hom.map_smul (e r) x }
  map_id := by intros; ext; rfl
  map_comp := by intros; ext; rfl }

/--
For any isomorphic rings `R` and `S`, the category of finitely generated modules over `R` and `S`
are equivalent.
-/
@[simps]
def _root_.RingEquiv.toFGModuleCatEquivalence : FGModuleCat R ≌ FGModuleCat S where
  functor := e.toFGModuleCatEquivalenceFunctor
  inverse := e.toFGModuleCatEquivalenceInverse
  unitIso :=
  { hom :=
    { app := fun X ↦
      FGModuleCat.ofHom <|
      { toFun := fun x ↦ x
        map_add' := by intros; rfl
        map_smul' := by
          intro r x
          exact (congr_arg (· • x) <| e.symm_apply_apply r).symm }
      naturality := by intros; ext; rfl }
    inv :=
    { app := fun X ↦ FGModuleCat.ofHom <|
      { toFun := fun x ↦ x
        map_add' := by intros; rfl
        map_smul' := by
          intro r x
          let m : Module S X := Module.compHom X e.symm.toRingHom
          have m_def (s : S) (x : X) : m.smul s x = e.symm s • x := rfl
          let m' : Module R X := Module.compHom X e.toRingHom
          have m'_def (r : R) (x : X) : m'.smul r x = m.smul (e r) x := rfl
          change m'.smul r x = X.1.3.smul r x
          rw [m'_def, m_def, e.symm_apply_apply]
          rfl }
      naturality := by intros; ext; rfl }
    hom_inv_id := by ext; rfl
    inv_hom_id := by ext; rfl }
  counitIso :=
  { hom :=
    { app := fun X ↦ FGModuleCat.ofHom <|
      { toFun := fun x ↦ x
        map_add' := by intros; rfl
        map_smul' := by
          intro r x
          let m : Module R X := Module.compHom X e.toRingHom
          have m_def (s : R) (x : X) : m.smul s x = e s • x := rfl
          let m' : Module S X := Module.compHom X e.symm.toRingHom
          have m'_def (r : S) (x : X) : m'.smul r x = m.smul (e.symm r) x := rfl
          change m'.smul r x = X.1.3.smul r x
          rw [m'_def, m_def, e.apply_symm_apply]
          rfl }
      naturality := by intros; ext; rfl }
    inv :=
    { app := fun X ↦ FGModuleCat.ofHom <|
      { toFun := fun x ↦ x
        map_add' := by intros; rfl
        map_smul' := by
          intro r x
          exact (congr_arg (· • x) <| e.apply_symm_apply r).symm }
      naturality := by intros; ext; rfl }
    hom_inv_id := by ext; rfl
    inv_hom_id := by ext; rfl }
  functor_unitIso_comp := by intros; ext; rfl

end Equivalence

section noetherian

variable {J : Type} [SmallCategory J] [FinCategory J]

variable {R : Type v} [Ring R] [IsNoetherianRing R]

instance {J : Type} [Finite J] (Z : J → ModuleCat R) [∀ j, Module.Finite R (Z j)] :
    Module.Finite R (∏ᶜ fun j => Z j : ModuleCat R) := by
  haveI : Module.Finite R (ModuleCat.of R (∀ j, Z j)) := by unfold ModuleCat.of; infer_instance
  apply Module.Finite.of_injective (ModuleCat.piIsoPi _).hom.hom
    ((ModuleCat.mono_iff_injective _).1 _)
  exact IsIso.mono_of_iso (ModuleCat.piIsoPi fun j ↦ Z j).hom

instance (F : J ⥤ FGModuleCat R) :
    Module.Finite R (limit (F ⋙ forget₂ (FGModuleCat R) (ModuleCat.{v} R)) : ModuleCat.{v} R) :=
  haveI : ∀ j, Module.Finite R ((F ⋙ forget₂ (FGModuleCat R) (ModuleCat.{v} R)).obj j) := by
    intro j; change Module.Finite R (F.obj j); infer_instance
  haveI : IsNoetherian R (ModuleCat.of R $
      (i : J) → ((F ⋙ forget₂ (FGModuleCat R) (ModuleCat R)).obj i)) :=
    inferInstanceAs $ IsNoetherian R $
      (i : J) → (F ⋙ forget₂ (FGModuleCat R) (ModuleCat R)).obj i
  haveI : IsNoetherian R
      (∏ᶜ fun j ↦ (F ⋙ forget₂ (FGModuleCat R) (ModuleCat R)).obj j : ModuleCat R) :=
    isNoetherian_of_linearEquiv (ModuleCat.piIsoPi _).symm.toLinearEquiv

  Module.Finite.of_injective
    (limitSubobjectProduct (F ⋙ forget₂ (FGModuleCat R) (ModuleCat.{v} R))).hom
    ((ModuleCat.mono_iff_injective _).1 inferInstance)

/-- The forgetful functor from `FGModuleCat R` to `ModuleCat R` creates all finite limits when `R`
is Noetherian. -/
noncomputable def forget₂CreatesLimitOfNoetherian (F : J ⥤ FGModuleCat R) :
    CreatesLimit F (forget₂ (FGModuleCat R) (ModuleCat.{v} R)) :=
  createsLimitOfFullyFaithfulOfIso
    ⟨(limit (F ⋙ forget₂ (FGModuleCat R) (ModuleCat.{v} R)) : ModuleCat.{v} R), inferInstance⟩
    (Iso.refl _)

noncomputable instance : CreatesLimitsOfShape J (forget₂ (FGModuleCat R) (ModuleCat.{v} R)) where
  CreatesLimit {F} := forget₂CreatesLimitOfNoetherian F

instance (J : Type) [Category J] [FinCategory J] :
    HasLimitsOfShape J (FGModuleCat.{v} R) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (forget₂ (FGModuleCat R) (ModuleCat.{v} R))

instance : HasFiniteLimits (FGModuleCat R) where
  out _ _ _ := inferInstance

noncomputable instance : PreservesFiniteLimits (forget₂ (FGModuleCat R) (ModuleCat.{v} R)) where
  preservesFiniteLimits _ _ _ := inferInstance

end noetherian

end FGModuleCat
