/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import DimensionTheory.Module.FGModuleCat.Kernels

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Exact
import Mathlib.Algebra.Category.FGModuleCat.Limits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The category of finitely generated modules over a Noetherian ring is abelian.

This file is basically a copy of `Algebra/ModuleCat/Abelian.lean`
-/

open CategoryTheory CategoryTheory.Limits

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

namespace FGModuleCat

variable {M N : FGModuleCat R} (f : M ⟶ N)

/--
A monomorphism between finitely generated modules is a normal monomorphism
-/
noncomputable def normalMono (hf : Mono f) : NormalMono f where
  Z := of R (N ⧸ LinearMap.range f)
  g := f.range.mkQ
  w := LinearMap.range_mkQ_comp _
  isLimit :=
    IsKernel.isoKernel _ _ (kernelIsLimit _)
      (LinearEquiv.toFGModuleCatIso
        ((Submodule.quotEquivOfEqBot _ (ker_eq_bot_of_mono _)).symm ≪≫ₗ
          (LinearMap.quotKerEquivRange f ≪≫ₗ
          LinearEquiv.ofEq _ _ (Submodule.ker_mkQ _).symm))) <| by ext; rfl

/--
An epimorphism between finitely generated modules is a normal epimorphism
-/
noncomputable def normalEpi (hf : Epi f) : NormalEpi f where
  W := of R (LinearMap.ker f)
  g := (LinearMap.ker f).subtype
  w := LinearMap.comp_ker_subtype _
  isColimit :=
    letI : Module.Finite R N.obj := N.2
    IsCokernel.cokernelIso _ _ (cokernelIsColimit _)
      (LinearEquiv.toFGModuleCatIso
        (Submodule.quotEquivOfEq _ _ (Submodule.range_subtype _) ≪≫ₗ
            LinearMap.quotKerEquivRange f ≪≫ₗ
          LinearEquiv.ofTop _ (range_eq_top_of_epi _))) <| by ext; rfl

noncomputable instance abelian_of_noetherian : Abelian (FGModuleCat R) where
  normalMonoOfMono := normalMono
  normalEpiOfEpi := normalEpi
  has_cokernels := hasCokernels_fgModuleCat

instance : HasForget₂ (FGModuleCat R) Ab where
  forget₂ :=
  { obj := fun x => .of x
    map := fun f => AddCommGrp.ofHom f }

instance : (forget₂ (FGModuleCat R) Ab).Additive := {}

noncomputable instance : PreservesFiniteLimits (forget₂ (FGModuleCat R) Ab) := by
  change PreservesFiniteLimits (forget₂ (FGModuleCat R) (ModuleCat R) ⋙ forget₂ (ModuleCat R) Ab)
  apply compPreservesFiniteLimits

noncomputable instance : PreservesFiniteLimits (forget (FGModuleCat R)) := by
  change PreservesFiniteLimits (forget₂ (FGModuleCat R) (ModuleCat R) ⋙ forget (ModuleCat R))
  apply compPreservesFiniteLimits

section exact

section image

@[simps]
noncomputable def imageFactorisation {M N : FGModuleCat R} (f : M ⟶ N) : ImageFactorisation f where
  F :=
  { I := .of R (LinearMap.range f)
    m := Submodule.subtype (LinearMap.range f)
    m_mono := by
      rw [ConcreteCategory.mono_iff_injective_of_preservesPullback]
      exact Subtype.val_injective
    e := LinearMap.rangeRestrict f
    fac := rfl }
  isImage :=
  { lift := fun F ↦
    { toFun := fun x => F.e <| x.2.choose
      map_add' := fun x y => by
        have := F.m_mono
        rw [ConcreteCategory.mono_iff_injective_of_preservesPullback] at this
        simp only [obj_carrier, id_eq, eq_mpr_eq_cast]
        apply this
        rw [← map_add]
        change (F.e ≫ F.m) _ = (F.e ≫ F.m) _
        rw [F.fac]
        rw [map_add]
        generalize_proofs _ _ _ h1 h2 h3
        rw [h1.choose_spec, h2.choose_spec, h3.choose_spec]
        rfl
      map_smul' := fun r x => by
        have := F.m_mono
        rw [ConcreteCategory.mono_iff_injective_of_preservesPullback] at this
        simp only [obj_carrier, id_eq, eq_mpr_eq_cast, RingHom.id_apply]
        rw [← map_smul]
        apply this
        change (F.e ≫ F.m) _ = (F.e ≫ F.m) _
        rw [F.fac]
        rw [map_smul]
        generalize_proofs _ _ _ h1 h2
        rw [h1.choose_spec, h2.choose_spec]
        rfl }
    lift_fac := fun F => by
      ext ⟨x, hx⟩
      dsimp only [id_eq, eq_mpr_eq_cast, obj_carrier, eq_mp_eq_cast, AddHom.toFun_eq_coe,
        AddHom.coe_mk, RingHom.id_apply]
      change (F.e ≫ F.m) _ = x
      rw [F.fac]
      generalize_proofs _ _ h
      rw [h.choose_spec] }

instance hasImages_fgModuleCat : HasImages (FGModuleCat R) where
  has_image f :=
  { exists_image := ⟨imageFactorisation f⟩ }

noncomputable def imageIsoRange {G H : FGModuleCat R} (f : G ⟶ H) :
    image f ≅ FGModuleCat.of R (LinearMap.range f) :=
  IsImage.isoExt (Image.isImage f) (imageFactorisation f).isImage

@[simp]
lemma imageIsoRange_hom_comp {G H : FGModuleCat R} (f : G ⟶ H) :
    (imageIsoRange f).hom ≫ Submodule.subtype (LinearMap.range f) = image.ι _ := by
  ext : 1
  rw [← Category.assoc, imageIsoRange]
  simp only [IsImage.isoExt_hom, image.isImage_lift, image.fac_lift, imageFactorisation_F_e,
    obj_carrier, image.fac]
  rfl

@[simp]
lemma imageIsoRange_inv_comp {G H : FGModuleCat R} (f : G ⟶ H) :
    (imageIsoRange f).inv ≫ image.ι _ = Submodule.subtype (LinearMap.range f) := by
  simp only [imageIsoRange, IsImage.isoExt_inv, IsImage.lift_ι, imageFactorisation_F_m]

end image

open CategoryTheory

variable {A B C : FGModuleCat R} (f : A ⟶ B) (g : B ⟶ C)

open LinearMap

theorem exact_iff (S : ShortComplex (FGModuleCat R)) :
    S.Exact ↔ LinearMap.range S.f = LinearMap.ker S.g := by
  rw [ShortComplex.exact_iff_image_eq_kernel]
  constructor
  · intro h
    obtain ⟨⟨a, _, ha⟩, ⟨b, _, hb⟩, hab, hba⟩ := Quotient.exact h
    dsimp at a b
    simp only [Functor.id_obj, Functor.const_obj_obj, MonoOver.mk'_obj, Over.mk_left,
      equalizer_as_kernel, Functor.id_map, Over.mk_hom, Discrete.functor_map_id,
      Category.comp_id] at ha hb hab hba
    rw [CommaMorphism.ext_iff] at hab hba
    simp only [Functor.id_obj, Functor.const_obj_obj, MonoOver.mk'_obj, Over.mk_left,
      CostructuredArrow.right_eq_id, and_true] at hab hba
    change a ≫ b = 𝟙 (image _) at hab
    change b ≫ a = 𝟙 (kernel _) at hba
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact congr($S.zero x)
    · let G := kernelIsoKer S.g
      let F := imageIsoRange S.f
      intro x hx
      simp only [mem_range]
      use (F.hom <| b <| G.inv ⟨x, hx⟩).2.choose
      rw [(F.hom <| b <| G.inv ⟨x, hx⟩).2.choose_spec]
      change Submodule.subtype _ _ = x
      change ((G.inv ≫ b ≫ F.hom) ≫ (range S.f).subtype <| _) = x
      simp only [Category.assoc]
      rw [imageIsoRange_hom_comp, hb, kernelIsoKer_inv_kernel_ι]
      rfl
  · intro eq
    apply Quotient.sound'
    refine ⟨⟨(imageIsoRange S.f).hom ≫ Submodule.inclusion (eq ▸ by rfl) ≫
      (kernelIsoKer S.g).inv, 𝟙 _, ?_⟩, ⟨(kernelIsoKer S.g).hom ≫
        Submodule.inclusion (eq ▸ by rfl) ≫ (imageIsoRange S.f).inv, 𝟙 _,  ?_⟩, ?_, ?_⟩
    · simp only [Functor.id_obj, Functor.const_obj_obj, MonoOver.mk'_obj, Over.mk_left,
        equalizer_as_kernel, Functor.id_map, Over.mk_hom, Category.assoc, kernelIsoKer_inv_kernel_ι,
        ← imageIsoRange_hom_comp, Discrete.functor_map_id, Category.comp_id,
        Iso.cancel_iso_hom_left]
      rfl
    · simp only [Functor.id_obj, Functor.const_obj_obj, equalizer_as_kernel, MonoOver.mk'_obj,
        Over.mk_left, Functor.id_map, Over.mk_hom, Category.assoc, imageIsoRange_inv_comp, ←
        kernelIsoKer_hom_ker_subtype, Discrete.functor_map_id, Category.comp_id,
        Iso.cancel_iso_hom_left]
      rfl
    · rw [CommaMorphism.ext_iff]
      simp only [Functor.id_obj, Functor.const_obj_obj, MonoOver.mk'_obj, Over.mk_left,
        equalizer_as_kernel, CostructuredArrow.right_eq_id, and_true]
      change (_ ≫ _ ≫ _) ≫ (_ ≫ _ ≫ _) = 𝟙 (image S.f)
      simp only [Functor.id_obj, Functor.const_obj_obj, MonoOver.mk'_obj, Over.mk_left,
        Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc _ _ (imageIsoRange S.f).inv]
      exact (imageIsoRange S.f).hom_inv_id
    · rw [CommaMorphism.ext_iff]
      simp only [Functor.id_obj, Functor.const_obj_obj, equalizer_as_kernel, MonoOver.mk'_obj,
        Over.mk_left, CostructuredArrow.right_eq_id, and_true]
      change (_ ≫ _ ≫ _) ≫ (_ ≫ _ ≫ _) = 𝟙 (kernel S.g)
      simp only [Functor.id_obj, Functor.const_obj_obj, MonoOver.mk'_obj, Over.mk_left,
        Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc _ _ (kernelIsoKer S.g).inv]
      exact (kernelIsoKer S.g).hom_inv_id

theorem exact_iff' (S : ShortComplex (FGModuleCat R)) :
    S.Exact ↔ Function.Exact S.f S.g := by
  rw [exact_iff, LinearMap.exact_iff]
  aesop

end exact

end FGModuleCat
