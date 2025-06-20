/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import DimensionTheory.missing_lemmas.FGModuleCat
import DimensionTheory.Module.FGModuleCat.EpiMono

import Mathlib.CategoryTheory.ConcreteCategory.Elementwise

/-!
# The concrete (co)kernels in the category of finitely generated modules over a Noetherian ring.

This file is almost a copy of `Algebra/ModuleCat/Kernels.lean`
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace FGModuleCat

variable {R : Type u} [Ring R] [IsNoetherianRing R]

section

variable {M N : FGModuleCat R} (f : M ⟶ N)

/-- The kernel cone induced by the concrete kernel. -/
def kernelCone : KernelFork f :=
  KernelFork.ofι (Z := .of R (LinearMap.ker f.hom)) (FGModuleCat.ofHom <| Submodule.subtype _) <| by ext x; cases x; aesop

/-- The kernel of a linear map is a kernel in the categorical sense. -/
def kernelIsLimit : IsLimit (kernelCone (R := R) f) :=
  Fork.IsLimit.mk _
    (fun s ↦ FGModuleCat.ofHom <|  LinearMap.codRestrict (LinearMap.ker f.hom) (Fork.ι s).hom fun c =>
        LinearMap.mem_ker.2 <| by
          rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
          erw [s.condition, HasZeroMorphisms.comp_zero (Fork.ι s) N]
          rfl)
    (fun s => by ext : 1; exact LinearMap.subtype_comp_codRestrict _ _ _) <| by
    intro s m h
    ext : 1
    exact LinearMap.ext fun x => Subtype.ext_iff_val.2 (by simp [← h]; rfl)

/-- The cokernel cocone induced by the projection onto the quotient. -/
def cokernelCocone : CokernelCofork f :=
  CokernelCofork.ofπ (Z := .of R (N ⧸ LinearMap.range f.hom)) (FGModuleCat.ofHom <| Submodule.mkQ _) <| by
    ext : 1
    exact LinearMap.range_mkQ_comp _

/-- The projection onto the quotient is a cokernel in the categorical sense. -/
def cokernelIsColimit : IsColimit (cokernelCocone f) :=
  Cofork.IsColimit.mk _
    (fun s => FGModuleCat.ofHom <|
      f.hom.range.liftQ (Cofork.π s).hom <| LinearMap.range_le_ker_iff.2 <| congr($(CokernelCofork.condition s).hom))
    (fun s => by ext : 1; exact f.hom.range.liftQ_mkQ (Cofork.π s).hom _) fun s m h => by
    let f : N ⟶ .of R (N ⧸ LinearMap.range f.hom) := FGModuleCat.ofHom (LinearMap.range f.hom).mkQ
    haveI : Epi f := (epi_iff_range_eq_top _).mpr (Submodule.range_mkQ _)
    exact (cancel_epi f).1 h

end

/-- The category of R-modules has kernels, given by the inclusion of the kernel submodule. -/
instance hasKernels_fgModuleCat : HasKernels (FGModuleCat R) :=
  ⟨fun f => HasLimit.mk ⟨_, kernelIsLimit f⟩⟩

omit [IsNoetherianRing R] in
/-- The category of R-modules has cokernels, given by the projection onto the quotient. -/
instance hasCokernels_fgModuleCat : HasCokernels (FGModuleCat R) :=
  ⟨fun f => HasColimit.mk ⟨_, cokernelIsColimit f⟩⟩

open FGModuleCat

attribute [local instance] hasCokernels_fgModuleCat

variable {G H : FGModuleCat R} (f : G ⟶ H)

/-- The categorical kernel of a morphism in `ModuleCat`
agrees with the usual module-theoretical kernel.
-/
noncomputable def kernelIsoKer {G H : FGModuleCat R} (f : G ⟶ H) :
    -- Porting note: broken dot notation
    kernel f ≅ FGModuleCat.of R (LinearMap.ker f.hom) :=
  limit.isoLimitCone ⟨_, kernelIsLimit f⟩

-- We now show this isomorphism commutes with the inclusion of the kernel into the source.
@[simp, elementwise]
    -- Porting note: broken dot notation
theorem kernelIsoKer_inv_kernel_ι : (kernelIsoKer f).inv ≫ kernel.ι f =
    FGModuleCat.ofHom (LinearMap.ker f.hom).subtype :=
  limit.isoLimitCone_inv_π _ _

@[simp, elementwise]
theorem kernelIsoKer_hom_ker_subtype :
    -- Porting note: broken dot notation
    (kernelIsoKer f).hom ≫ FGModuleCat.ofHom (LinearMap.ker f.hom).subtype = kernel.ι f :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) WalkingParallelPair.zero

/-- The categorical cokernel of a morphism in `ModuleCat`
agrees with the usual module-theoretical quotient.
-/
noncomputable def cokernelIsoRangeQuotient {G H : FGModuleCat R} (f : G ⟶ H) :
    -- Porting note: broken dot notation
    cokernel f ≅ FGModuleCat.of R (H ⧸ LinearMap.range f.hom) :=
  colimit.isoColimitCocone ⟨_, cokernelIsColimit f⟩

omit [IsNoetherianRing R] in
-- We now show this isomorphism commutes with the projection of target to the cokernel.
@[simp, elementwise]
theorem cokernel_π_cokernelIsoRangeQuotient_hom :
    cokernel.π f ≫ (cokernelIsoRangeQuotient f).hom = FGModuleCat.ofHom f.hom.range.mkQ :=
  colimit.isoColimitCocone_ι_hom (F := parallelPair f 0) (t := ⟨_, cokernelIsColimit f⟩) .one



omit [IsNoetherianRing R] in
@[simp, elementwise]
theorem range_mkQ_cokernelIsoRangeQuotient_inv :
    FGModuleCat.ofHom f.hom.range.mkQ ≫ (cokernelIsoRangeQuotient f).inv = cokernel.π f :=
  colimit.isoColimitCocone_ι_inv ⟨_, cokernelIsColimit f⟩ WalkingParallelPair.one

omit [IsNoetherianRing R] in
theorem cokernel_π_ext {M N : FGModuleCat R} (f : M ⟶ N) {x y : N} (m : M) (w : x = y + f m) :
    cokernel.π f x = cokernel.π f y := by
  subst w
  simpa only [map_add, add_right_eq_self] using cokernel.condition_apply f m

end FGModuleCat
