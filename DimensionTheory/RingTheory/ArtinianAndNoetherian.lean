/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import DimensionTheory.Module.Length
import DimensionTheory.RingTheory.KrullDimension
import DimensionTheory.missing_lemmas.Noetherian
import DimensionTheory.missing_lemmas.Artinian
import DimensionTheory.missing_lemmas.AboutSheafConditions

import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts
import Mathlib.Topology.Separation.Basic
import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Properties of Artinian Rings

- `IsArtinianRing.equivProdLocalization` : if `R` is an artinian ring, then `R` is isomorphic to
  product of all its prime localizations
- Artinian rings are Noetherian.

## Implementations notes

The proof here probably does not generalize to non-commutative cases.

-/

open TopologicalSpace AlgebraicGeometry Opposite CategoryTheory

open BigOperators

universe u
variable (R : Type u) [CommRing R]

section zeroDimensionalAndFinite

variable [dim0 : Fact <| ringKrullDim R = 0] [Finite (PrimeSpectrum R)]

instance t1_space_of_dim_zero : T1Space (PrimeSpectrum R) where
  t1 p := PrimeSpectrum.isClosed_singleton_iff_isMaximal _ |>.mpr <|
    p.isPrime.isMaximal_of_dim_zero dim0.out

instance discrete_of_dim_zero : DiscreteTopology (PrimeSpectrum R) :=
  Finite.instDiscreteTopology

variable {R}

/--
Cover of Spec of an artinian ring by singleton sets.
-/
@[simps]
def openCover (i : PrimeSpectrum R) : Opens (PrimeSpectrum R) :=
  ⟨{i}, by continuity⟩

lemma openCover.pairwiseDisjoint (i j : PrimeSpectrum R) (hij : i ≠ j) :
    openCover i ⊓ openCover j = ⊥ := by
  ext p
  simp only [ge_iff_le, Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, Opens.coe_bot,
    Set.mem_empty_iff_false, iff_false, not_and]
  intro hp
  rw [Set.mem_singleton_iff.mp hp]
  contrapose! hij
  ext1
  rw [Set.mem_singleton_iff.mp hij]

variable (R) in
lemma openCover.is_cover : ⨆ (i : PrimeSpectrum R), openCover i = ⊤ :=
  eq_top_iff.mpr <| fun p _ ↦ by simp

instance (i : PrimeSpectrum R) : Unique (openCover i) where
  default := ⟨i, by simp [openCover]⟩
  uniq p := Subtype.ext <| by rw [Set.mem_singleton_iff.mp p.2]; rfl

/--
𝒪(Spec R) = ∏ᵢ Rᵢ where `i` runs through prime ideals.
-/
noncomputable def sectionsOnOpenCover (i : PrimeSpectrum R) :
    (Spec.structureSheaf R).presheaf.obj (op <| openCover i) ≅
    CommRingCat.of <| Localization.AtPrime i.asIdeal :=
  let e (x : openCover i) :  Localization.AtPrime i.asIdeal ≃+* Localization.AtPrime x.1.asIdeal :=
    IsLocalization.ringEquivOfRingEquiv
      (S := Localization.AtPrime i.asIdeal)
      (Q := Localization.AtPrime x.1.asIdeal)
      (M := i.asIdeal.primeCompl) (T := x.1.asIdeal.primeCompl) (RingEquiv.refl R) <| by
      rw [Set.mem_singleton_iff.mp x.2]; simp
  RingEquiv.toCommRingCatIso
  { toFun := fun f ↦ f.1 ⟨i, by simp only [openCover, unop_op]; exact Set.mem_singleton _⟩
    invFun := fun q ↦ ⟨fun x ↦ e _ q, fun x ↦ by
        simp_rw [Set.mem_singleton_iff.mp x.2]
        induction' q using Localization.induction_on with d
        rcases d with ⟨r, ⟨s, hs⟩⟩
        refine ⟨(openCover i), Set.mem_singleton _, 𝟙 _, r, s, fun p ↦ ⟨?_, ?_⟩⟩
        · rw [Set.mem_singleton_iff.mp p.2]; exact hs
        · dsimp [e]
          rw [Localization.mk_eq_mk', IsLocalization.map_mk']
          erw [IsLocalization.mk'_spec]
          rfl⟩
    left_inv := by
      rintro ⟨f, hf⟩
      simp only [unop_op, StructureSheaf.isLocallyFraction_pred, id_eq,
        IsLocalization.ringEquivOfRingEquiv_apply, RingEquiv.coe_ringHom_refl, e]
      refine Subtype.ext <| funext fun (x : openCover i) ↦ ?_
      simp only [unop_op]
      have eq1 : x = (⟨i, by simp [openCover]⟩ : openCover i) := Subsingleton.elim _ _
      rw [eq1]
      simp only [IsLocalization.map_id]
    right_inv := by
      intro p
      simp only [unop_op, id_eq, IsLocalization.ringEquivOfRingEquiv_apply,
        RingEquiv.coe_ringHom_refl, IsLocalization.map_id, e]
    map_mul' := fun x y ↦ by
      simp only [unop_op, StructureSheaf.isLocallyFraction_pred, id_eq]
      rfl
    map_add' := fun x y ↦ by
      simp only [unop_op, StructureSheaf.isLocallyFraction_pred, id_eq]
      rfl }

variable (R) in
lemma globalSectionsEquivProd : Nonempty <|
    (Spec.structureSheaf R).presheaf.obj (op ⊤) ≅
    ∏ᶜ fun (i : PrimeSpectrum R) ↦ CommRingCat.of (Localization.AtPrime i.asIdeal) := by
  refine (Spec.structureSheaf R).sections_on_disjoint_opens_iso_product (openCover (R := R))
    openCover.pairwiseDisjoint |>.map fun e ↦ ?_ ≪≫ e ≪≫ ?_
  · fconstructor
    · exact (Spec.structureSheaf R).presheaf.map (Quiver.Hom.op <| homOfLE le_top)
    · exact (Spec.structureSheaf R).presheaf.map
        (Quiver.Hom.op <| homOfLE <| eq_top_iff.mp <| openCover.is_cover R)
    · aesop_cat
    · aesop_cat
  · fconstructor
    · exact Limits.Pi.map fun p ↦ (sectionsOnOpenCover p).hom
    · exact Limits.Pi.map fun p ↦ (sectionsOnOpenCover p).inv
    · aesop_cat
    · aesop_cat

lemma equivProdLocalization' : Nonempty <|
    R ≃+* ((i : PrimeSpectrum R) → Localization.AtPrime i.asIdeal) := by
  refine globalSectionsEquivProd R |>.map fun e ↦
    RingEquiv.ofHomInv (?_ : R →+* ((i : PrimeSpectrum R) → Localization.AtPrime i.asIdeal))
      (?_ : ((i : PrimeSpectrum R) → Localization.AtPrime i.asIdeal) →+* R) ?_ ?_
  · exact (CommRingCat.piIsoPi _ |>.hom).hom
      |>.comp e.hom.hom |>.comp (StructureSheaf.globalSectionsIso R).hom.hom
  · exact (StructureSheaf.globalSectionsIso R).inv.hom |>.comp e.inv.hom |>.comp
      (CommRingCat.piIsoPi
        fun (i : PrimeSpectrum R) ↦ CommRingCat.of <| Localization.AtPrime i.asIdeal).inv.hom
  · refine RingHom.ext fun r ↦ ?_
    simp [Functor.comp_obj, Discrete.functor_obj_eq_as, CommRingCat.coe_of,
      StructureSheaf.globalSectionsIso_inv, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      Iso.hom_inv_id_apply, RingHom.id_apply]
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
    erw [IsIso.hom_inv_id]
    rfl
  · refine RingHom.ext fun r ↦ ?_
    simp only [CommRingCat.coe_of, StructureSheaf.globalSectionsIso_inv, RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply, RingHom.id_apply]
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← RingHom.comp_apply, ← RingHom.comp_apply,
      ← RingHom.comp_apply, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
      ← CommRingCat.hom_comp, ← CommRingCat.hom_comp]

    erw [(StructureSheaf.globalSectionsIso R).inv_hom_id_assoc, e.inv_hom_id_assoc, Iso.inv_hom_id]
    rfl

/--
If $R$ is an artinian ring, then $R \cong \prod_{\mathfrak{p}}R_{\mathfrak{p}}$
-/
noncomputable def equivProdLocalization :
    R ≃+* ((i : PrimeSpectrum R) → Localization.AtPrime i.asIdeal) :=
  Classical.choice equivProdLocalization'

end zeroDimensionalAndFinite

section zeroDimensionalAndNoetherianLocal

lemma maximalIdeal_locally_nilpotent_of_zero_dimensional_local_ring
    [IsLocalRing R] (dim0 : ringKrullDim R = 0)
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) : ∃ (n : ℕ), x ^ n = 0 := by
  suffices eq1 : IsLocalRing.maximalIdeal R = nilradical R by
    rw [eq1] at hx; exact hx
  rw [nilradical_eq_sInf]
  rw [show sInf {J : Ideal R | Ideal.IsPrime J} = sInf {J : Ideal R | Ideal.IsMaximal J} by
    · congr 1
      ext J
      exact ⟨fun h ↦ Ideal.IsPrime.isMaximal_of_dim_zero h dim0, Ideal.IsMaximal.isPrime⟩,
    show {J : Ideal R | Ideal.IsMaximal J} = {IsLocalRing.maximalIdeal R} by
    · ext J
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨fun h ↦ IsLocalRing.eq_maximalIdeal h,
        by rintro rfl; exact IsLocalRing.maximalIdeal.isMaximal R⟩]
  simp only [csInf_singleton]

lemma _root_.Ideal.pow_eq_span (n : ℕ) (I : Ideal R) :
    I ^ n =
    Ideal.span { r : R | ∃ s : Fin n → I, r = ∏ i : Fin n, (s i).1 } := by
  symm
  induction' n with n ih
  · simp

  refine Submodule.span_eq_of_le _ ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    rw [Fin.prod_univ_succ, pow_succ', ← ih]
    exact Ideal.mul_mem_mul (s 0).2 (Submodule.subset_span ⟨_, rfl⟩)
  · rw [pow_succ']
    rw [Ideal.mul_le]
    intro r hr s hs
    simp only [LinearMap.mul_apply', Ideal.submodule_span_eq]
    rw [← ih] at hs
    refine Submodule.span_induction (hx := hs) ?_ ?_ ?_ ?_
    · rintro _ ⟨t, rfl⟩
      refine Ideal.subset_span ⟨Fin.cons ⟨r, hr⟩ t, ?_⟩
      conv_rhs => rw [Fin.prod_univ_succ]
      simp
    · simp
    · intro t₁ t₂ _ _ h₁ h₂
      rw [mul_add]
      exact Submodule.add_mem _ h₁ h₂
    · intro t x _ hx
      rw [smul_eq_mul, ← mul_assoc, mul_comm r t, mul_assoc]
      exact Ideal.mul_mem_left _ _ hx

lemma IsNoetherianRing.pow_le_of_le_radical [noeth : IsNoetherianRing R] (I J : Ideal R)
    (hIJ : I ≤ J.radical) : ∃ (n : ℕ), I ^ n ≤ J := by
  classical
  obtain ⟨S, rfl⟩ := isNoetherianRing_iff_ideal_fg _ |>.mp noeth I
  induction' S using Finset.induction with r S _ ih
  · simp only [Finset.coe_empty, Ideal.span_empty]
    exact ⟨1, by simp⟩
  · simp only [Finset.coe_insert, Ideal.span_insert, sup_le_iff] at hIJ ⊢
    obtain ⟨n, hn⟩ := ih hIJ.2
    rw [Ideal.span_le, Ideal.span_le] at hIJ
    simp only [Set.singleton_subset_iff, SetLike.mem_coe] at hIJ
    obtain ⟨m, hm⟩ := hIJ.1
    refine ⟨n + m, ?_⟩
    rw [Ideal.pow_eq_span, Ideal.span_le]
    rintro _ ⟨t, rfl⟩
    have H (i : Fin (n + m)) : (t i).1 ∈ Ideal.span {r} ⊔ Ideal.span S := (t i).2
    simp_rw [Ideal.mem_span_singleton_sup] at H
    choose a b hab1 hab2 using H

    simp_rw [← hab2]
    rw [Finset.prod_add]
    refine sum_mem fun s _ ↦ ?_
    by_cases s_eq : m ≤ s.card
    · refine Ideal.mul_mem_right _ _ ?_
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const]
      refine Ideal.mul_mem_left _ _ ?_
      rw [show s.card = m + (s.card - m) by rw [Nat.add_sub_cancel' s_eq], pow_add]
      exact Ideal.mul_mem_right _ _ (by assumption)

    · refine Ideal.mul_mem_left _ _ ?_
      simp only [not_le] at s_eq
      have s_eq' : n ≤ Finset.card (Finset.univ \ s) := by
        simp only [Finset.subset_univ, Finset.card_sdiff, Finset.card_fin]
        rw [Nat.add_sub_assoc (le_of_lt s_eq)]
        norm_num
      let e := (Finset.univ \ s).equivFin

      rw [← Finset.prod_attach,
        show ∏ a ∈ (Finset.univ \ s).attach, b a =
          ∏ a : Fin ((Finset.univ \ s).card), b (e.symm a) by
        rw [Finset.prod_equiv e] <;> aesop]

      have eq0 : (Finset.univ \ s).card = n + ((Finset.univ \ s).card - n) :=
        Nat.add_sub_cancel' s_eq' |>.symm
      let e' := finCongr eq0
      rw [show ∏ a : Fin ((Finset.univ \ s).card), b (e.symm a) =
        ∏ a : Fin (n + ((Finset.univ \ s).card - n)), b (e.symm <| e'.symm a) by
          rw [Finset.prod_equiv e']
          · simp
          · intro i
            simp only [Finset.mem_univ, finCongr_symm, forall_true_left]
            congr,
        Fin.prod_univ_add]
      refine Ideal.mul_mem_right _ _ <| hn ?_
      rw [Ideal.pow_eq_span]
      set g : Fin n → R := _
      change ∏ i : Fin n, g i ∈ _
      exact Ideal.subset_span ⟨fun i ↦ ⟨g i, hab1 _⟩, rfl⟩

lemma IsNoetherianRing.nilpotent_maximalIdeal_of_zero_dimensional_localRing
    [noeth : IsNoetherianRing R] [IsLocalRing R] (dim0 : ringKrullDim R = 0) :
    IsNilpotent (IsLocalRing.maximalIdeal R) := by
  obtain ⟨n, hn⟩ := IsNoetherianRing.pow_le_of_le_radical R (IsLocalRing.maximalIdeal R) ⊥
    (fun r hr ↦ maximalIdeal_locally_nilpotent_of_zero_dimensional_local_ring R dim0 r hr)
  exact ⟨n, by simpa using hn⟩

end zeroDimensionalAndNoetherianLocal


noncomputable section local_ring

namespace local_ring_with_nilpotent_maximal_ideal

variable [IsLocalRing R] [Nontrivial R]
variable [maximalIdeal_nilpotent : Fact <| IsNilpotent <| IsLocalRing.maximalIdeal (R := R)]

local notation "𝔪" => IsLocalRing.maximalIdeal (R := R)
local notation "κ" => IsLocalRing.ResidueField (R := R)

omit [Nontrivial R] in
/--
Maximal ideal of an artinian local ring is nilpotent.
-/
lemma exists_K : ∃ K : ℕ, 𝔪 ^ K = 0 := maximalIdeal_nilpotent.out

/--
Let `K` be the smallest number such that `𝔪 ^ K = 0`
-/
def K : ℕ := exists_K R |>.choose

omit [Nontrivial R] in
lemma K_spec : 𝔪 ^ K R = 0 := exists_K R |>.choose_spec

/--
Construct a series by `0 ≤ 𝔪ᵏ⁻¹ ≤ 𝔪ᵏ⁻² ≤ ... ≤ 𝔪 ≤ R`
-/
@[simps]
def series : RelSeries ((· ≤ ·) : Ideal R → Ideal R → Prop) where
  length := K R
  toFun i := 𝔪 ^ (K R - i.1)
  step i := by
    simp only [Fin.coe_castSucc, Fin.val_succ]
    apply Ideal.pow_le_pow_right
    apply Nat.sub_le_sub_left
    norm_num

omit [Nontrivial R] in
@[simp] lemma series_head : (series R).head = 0 := show 𝔪 ^ (K R - 0) = 0 from by
  simp [K_spec]

omit [Nontrivial R] in
@[simp] lemma series_last : (series R).last = ⊤ := show 𝔪 ^ (K R - K R) = ⊤ from by
  simp

/--
Define the action of `R ⧸ 𝔪` on `𝔪ⁿ ⧸ 𝔪ⁿ⁺¹` by `[r] • [x] = [r • x]`
-/
def residualFieldActionOnQF (i : Fin (K R)) : κ →ₗ[R] Module.End R ((series R).qf i) :=
  Submodule.liftQ _ (LinearMap.lsmul _ _) fun r hr ↦ by
    simp only [series_length, series_toFun, Fin.val_succ, Fin.coe_castSucc, LinearMap.mem_ker]
    ext m
    simp only [LinearMap.lsmul_apply, LinearMap.zero_apply]
    induction' m using Quotient.inductionOn' with m
    simp only [series_length, series_toFun, Fin.val_succ, Fin.coe_castSucc,
      Submodule.Quotient.mk''_eq_mk]
    change Submodule.Quotient.mk (r • m) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    simp only [series_length, series_toFun, Fin.val_succ, Submodule.mem_comap, map_smulₛₗ,
      RingHom.id_apply, Submodule.coe_subtype, smul_eq_mul]
    have mem1 := m.2
    simp only [series_length, series_toFun, Fin.val_succ] at mem1
    have eq1 : 𝔪 ^ (K R - i) = 𝔪 * 𝔪 ^ (K R - (i + 1)) := by
      conv_rhs => lhs; rw [show 𝔪 = 𝔪 ^ 1 from pow_one _ |>.symm]
      rw [← pow_add, add_comm]
      congr
      rw [Nat.sub_add_eq, Nat.sub_add_cancel]
      apply Nat.sub_pos_of_lt i.2
    rw [eq1]
    refine Ideal.mul_mem_mul hr mem1

instance (i : Fin (K R)) : Module κ ((series R).qf i) where
  smul x := residualFieldActionOnQF R i x
  one_smul x := by
    change residualFieldActionOnQF R i 1 x = x
    induction' x using Quotient.inductionOn' with x
    erw [Submodule.liftQ_apply]
    simp
  mul_smul a b x := by
    change residualFieldActionOnQF R i (a * b) x = residualFieldActionOnQF R i a
      (residualFieldActionOnQF R i b x)
    induction' x using Quotient.inductionOn' with x
    induction' a using Quotient.inductionOn' with a
    induction' b using Quotient.inductionOn' with b
    delta residualFieldActionOnQF
    simp only [series_length, series_toFun, Fin.val_succ, Fin.coe_castSucc,
      Submodule.Quotient.mk''_eq_mk, Ideal.Quotient.mk_eq_mk]
    erw [Submodule.liftQ_apply, Submodule.liftQ_apply, Submodule.liftQ_apply]
    simp only [series_length, series_toFun, Fin.val_succ, Fin.coe_castSucc, LinearMap.lsmul_apply,
      map_smul]
    rw [mul_comm, mul_smul]
  smul_zero a := by
    change residualFieldActionOnQF R i a 0 = 0
    induction' a using Quotient.inductionOn' with a
    delta residualFieldActionOnQF
    simp
  smul_add a x y := by
    change residualFieldActionOnQF R i a (x + y) = residualFieldActionOnQF R i a x +
      residualFieldActionOnQF R i a y
    delta residualFieldActionOnQF
    induction' x using Quotient.inductionOn' with x
    induction' y using Quotient.inductionOn' with y
    induction' a using Quotient.inductionOn' with a
    simp
  add_smul a b x := by
    change residualFieldActionOnQF R i (a + b) x = residualFieldActionOnQF R i a x +
      residualFieldActionOnQF R i b x
    delta residualFieldActionOnQF
    induction' x using Quotient.inductionOn' with x
    induction' a using Quotient.inductionOn' with a
    induction' b using Quotient.inductionOn' with b
    simp
  zero_smul x := by
    change residualFieldActionOnQF R i 0 x = 0
    delta residualFieldActionOnQF
    induction' x using Quotient.inductionOn' with x
    simp

/--
A semilinear map from `𝔪ⁿ ⧸ 𝔪ⁿ⁺¹` as `R`-module to `𝔪ⁿ ⧸ 𝔪ⁿ⁺¹` as `R ⧸ 𝔪` module
-/
@[simps]
def id_κR (i : Fin (K R)) : (series R).qf i →ₛₗ[algebraMap R κ] (series R).qf i :=
{ toFun := id
  map_add' := fun _ _ ↦ rfl
  map_smul' := fun r m ↦ by
    induction' m using Quotient.inductionOn' with m
    simp only [series_length, series_toFun, Fin.val_succ, Fin.coe_castSucc,
      Submodule.Quotient.mk''_eq_mk, id_eq, IsLocalRing.ResidueField.algebraMap_eq]
    rfl }

instance : RingHomSurjective (algebraMap R κ) where
  is_surjective := Submodule.mkQ_surjective _

/--
The `R ⧸ 𝔪`-submodules of `𝔪ⁿ ⧸ 𝔪ⁿ⁺¹` are exactly the same as the `R`-submodules of `𝔪ⁿ ⧸ 𝔪ⁿ⁺¹`.
-/
@[simps]
def qfSubmoduleAgree (i : Fin (K R)) :
    Submodule κ ((series R).qf i) ≃o
    Submodule R ((series R).qf i) where
  toFun p := Submodule.comap (id_κR R i) p
  invFun q := Submodule.map (id_κR R i) q
  left_inv _ := Submodule.map_comap_eq_of_surjective (fun x ↦ ⟨x, rfl⟩) _
  right_inv _ := Submodule.comap_map_eq_of_injective (fun _ _ h ↦ h) _
  map_rel_iff' := ⟨id, id⟩

/--
The `R ⧸ 𝔪`-submodules of `𝔪ⁿ ⧸ 𝔪ⁿ⁺¹` are exactly the same as the `R`-submodules of `𝔪ⁿ ⧸ 𝔪ⁿ⁺¹`.
(reverse the order)
-/
@[simps!]
def qfSubmoduleAgree' (i : Fin (K R)) :
    (Submodule κ ((series R).qf i))ᵒᵈ ≃o
    (Submodule R ((series R).qf i))ᵒᵈ :=
  OrderIso.dual <| qfSubmoduleAgree R i

instance qf_artinian_R [IsArtinianRing R] (i : Fin (K R)) : IsArtinian R ((series R).qf i) := by
  change IsArtinian R (_ ⧸ _)
  infer_instance

instance qf_noetherian_R [IsNoetherianRing R] (i : Fin (K R)) :
    IsNoetherian R ((series R).qf i) := by
  change IsNoetherian R (_ ⧸ _)
  infer_instance

omit [Nontrivial R] in
lemma qf_artinian_κR_iff (i : Fin (K R)) :
    IsArtinian κ ((series R).qf i) ↔ IsArtinian R ((series R).qf i) := by
  rw [← monotone_stabilizes_iff_artinian, ← monotone_stabilizes_iff_artinian]
  fconstructor <;> intro h f
  · let f' : ℕ →o (Submodule κ ((series R).qf i))ᵒᵈ := OrderHom.comp ?_ f
    pick_goal 2
    · fconstructor
      · exact (qfSubmoduleAgree' R i).symm.toFun
      · intro p q h
        exact (qfSubmoduleAgree' R i).symm.monotone h
    obtain ⟨n, hn⟩ := h f'
    refine ⟨n, fun m hm ↦ ?_⟩
    specialize hn m hm
    exact (qfSubmoduleAgree' R i).symm.injective hn
  · let f' : ℕ →o (Submodule R ((series R).qf i))ᵒᵈ := OrderHom.comp ?_ f
    pick_goal 2
    · fconstructor
      · exact (qfSubmoduleAgree' R i).toFun
      · intro p q h
        exact (qfSubmoduleAgree' R i).monotone h
    obtain ⟨n, hn⟩ := h f'
    refine ⟨n, fun m hm ↦ ?_⟩
    specialize hn m hm
    exact (qfSubmoduleAgree' R i).injective hn

omit [Nontrivial R] in
lemma qf_noetherian_κR_iff (i : Fin (K R)) :
    IsNoetherian κ ((series R).qf i) ↔ IsNoetherian R ((series R).qf i) := by
  rw [← monotone_stabilizes_iff_noetherian, ← monotone_stabilizes_iff_noetherian]
  fconstructor <;> intro h f
  · let f' : ℕ →o (Submodule κ ((series R).qf i)) := OrderHom.comp ?_ f
    pick_goal 2
    · fconstructor
      · exact (qfSubmoduleAgree R i).symm.toFun
      · intro p q h
        exact (qfSubmoduleAgree R i).symm.monotone h
    obtain ⟨n, hn⟩ := h f'
    refine ⟨n, fun m hm ↦ ?_⟩
    specialize hn m hm
    exact (qfSubmoduleAgree' R i).symm.injective hn
  · let f' : ℕ →o (Submodule R ((series R).qf i)) := OrderHom.comp ?_ f
    pick_goal 2
    · fconstructor
      · exact (qfSubmoduleAgree R i).toFun
      · intro p q h
        exact (qfSubmoduleAgree R i).monotone h
    obtain ⟨n, hn⟩ := h f'
    refine ⟨n, fun m hm ↦ ?_⟩
    specialize hn m hm
    exact (qfSubmoduleAgree' R i).injective hn

instance qf_artinian_κ [IsArtinianRing R] (i : Fin (K R)) : IsArtinian κ ((series R).qf i) :=
  qf_artinian_κR_iff R i |>.mpr inferInstance

instance qf_noetherian_κ [IsNoetherianRing R] (i : Fin (K R)) : IsNoetherian κ ((series R).qf i) :=
  qf_noetherian_κR_iff R i |>.mpr inferInstance

instance qf_finiteLength_κ_of_artinian [IsArtinianRing R] (i : Fin (K R)) :
    FiniteLengthModule κ ((series R).qf i) := by
  suffices inst1 : IsFiniteLengthModule κ ((series R).qf i) from Classical.choice inst1.finite
  rw [finiteLengthModule_over_field_iff_finite_dimensional,
    ← Module.finite_iff_artinian_over_divisionRing]
  infer_instance

instance qf_finiteLength_κ_of_noetherian [IsNoetherianRing R] (i : Fin (K R)) :
    FiniteLengthModule κ ((series R).qf i) := by
  suffices inst1 : IsFiniteLengthModule κ ((series R).qf i) from Classical.choice inst1.finite
  rw [finiteLengthModule_over_field_iff_finite_dimensional]
  infer_instance

instance qf_finiteLength_R_of_artinian [IsArtinianRing R] (i : Fin (K R)) :
    FiniteLengthModule R ((series R).qf i) := by
  have i1 := isFiniteLengthModule_iff_restrictScalars R κ ((series R).qf i) |>.mp
    ⟨⟨qf_finiteLength_κ_of_artinian R i⟩⟩
  exact Classical.choice i1.1

instance qf_finiteLength_R_of_noetherian [IsNoetherianRing R] (i : Fin (K R)) :
    FiniteLengthModule R ((series R).qf i) := by
  have i1 := isFiniteLengthModule_iff_restrictScalars R κ ((series R).qf i) |>.mp
    ⟨⟨qf_finiteLength_κ_of_noetherian R i⟩⟩
  exact Classical.choice i1.1

/--
The last cumulative quotient factor is exactly `R`.
-/
def cdf_last_eq : (series R).cqf (Fin.last _) ≃ₗ[R] R :=
LinearEquiv.ofLinear
  (Submodule.liftQ _ (Submodule.subtype _) fun x hx ↦ by simpa using hx)
  { toFun := fun r ↦ Submodule.Quotient.mk ⟨r, by
      change r ∈ (series R).last
      rw [series_last]
      simp only [Submodule.mem_top]⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  (LinearMap.ext fun x ↦ by
    simp only [series_length, series_toFun, Fin.val_last, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.id_coe, id_eq]
    erw [Submodule.liftQ_apply]
    rfl)
  (LinearMap.ext fun x ↦ by
    induction' x using Quotient.inductionOn' with x
    simp only [series_length, series_toFun, Fin.val_last, Submodule.Quotient.mk''_eq_mk,
      LinearMap.id_coe, id_eq]
    erw [LinearMap.comp_apply]
    erw [Submodule.liftQ_apply, Submodule.Quotient.eq]
    simp)

end local_ring_with_nilpotent_maximal_ideal

end local_ring

namespace IsArtinianRing

variable [IsArtinianRing R]

instance : Finite (PrimeSpectrum R) := @Finite.of_equiv _ {I : Ideal R | I.IsPrime}
  (Set.finite_coe_iff.mpr <| IsArtinianRing.setOf_isPrime_finite R)
  ⟨fun x ↦ ⟨x.1, x.2⟩, fun x ↦ ⟨x.1, x.2⟩, fun _ ↦ by aesop, fun _ ↦ by aesop⟩

noncomputable instance : Fintype (PrimeSpectrum R) :=
  Classical.choice <| finite_iff_nonempty_fintype (PrimeSpectrum R) |>.mp inferInstance

instance isNoetherianRing_of_local [IsLocalRing R] : IsNoetherianRing R := by
  suffices i1 : IsFiniteLengthModule R R from isNoetherian_of_finiteLength R R
  have i2 : Fact (IsNilpotent (IsLocalRing.maximalIdeal R)) := by
    fconstructor
    have H := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
    rwa [IsLocalRing.jacobson_eq_maximalIdeal (h := by simp)] at H

  refine isFiniteLengthModule_congr (local_ring_with_nilpotent_maximal_ideal.cdf_last_eq R)
    (h := ?_)
  rw [RelSeries.cqf_finiteLength_iff_each_qf_finiteLength]
  intro j
  infer_instance

open Order
instance isNoetherianRing_of_isArtinianRing : IsNoetherianRing R := by
  rcases subsingleton_or_nontrivial R with H | H
  · exact isNoetherian_of_finite R R
  · letI : Fact (ringKrullDim R = 0) := ⟨ringKrullDim.eq_zero_of_isArtinianRing R⟩
    exact @isNoetherianRing_of_ringEquiv _ _ _ _ (f := equivProdLocalization.symm) <| IsNoetherianRing.Pi _

end IsArtinianRing

namespace IsNoetherianRing

variable [dim0 : Fact (ringKrullDim R = 0)] [IsNoetherianRing R]

noncomputable instance : Fintype (PrimeSpectrum R) := PrimeSpectrum.finTypeOfNoetherian dim0.out

instance isArtinianRing_of_local_dim0_noetherian [IsLocalRing R] : IsArtinianRing R := by
  suffices i1 : IsFiniteLengthModule R R from isArtinian_of_finiteLength R R
  have i2 : Fact (IsNilpotent (IsLocalRing.maximalIdeal R)) :=
  ⟨IsNoetherianRing.nilpotent_maximalIdeal_of_zero_dimensional_localRing _ dim0.out⟩

  refine isFiniteLengthModule_congr (local_ring_with_nilpotent_maximal_ideal.cdf_last_eq R)
    (h := ?_)
  rw [RelSeries.cqf_finiteLength_iff_each_qf_finiteLength]
  intros j
  infer_instance

open Order
instance : IsArtinianRing R := by
  rcases subsingleton_or_nontrivial R with H | _
  · exact isArtinian_of_finite
  · have i1 (i : PrimeSpectrum R) : IsNoetherianRing (Localization.AtPrime i.asIdeal) :=
      IsNoetherianRing.Localization (Ideal.primeCompl i.asIdeal) _
    have i2 (i : PrimeSpectrum R) : Fact (ringKrullDim (Localization.AtPrime i.asIdeal) = 0) := by
      fconstructor
      have : ringKrullDim (Localization.AtPrime i.asIdeal) ≤ ringKrullDim R :=
        krullDim_le_of_strictMono (fun p ↦
          ⟨IsLocalization.orderEmbedding i.asIdeal.primeCompl (Localization.AtPrime i.asIdeal) p.1,
            ?_⟩) ?_
      pick_goal 2
      · simp only [IsLocalization.orderEmbedding, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk]
        exact Ideal.IsPrime.comap _
      pick_goal 2
      · intro p q hpq
        simp only [IsLocalization.orderEmbedding, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk]
        change Ideal.comap _ _ < Ideal.comap _ _
        refine ⟨Ideal.comap_mono hpq.1, ?_⟩
        obtain ⟨x, hx1, hx2⟩ := Set.not_subset.mp hpq.2
        induction' x using Localization.induction_on with data
        rcases data with ⟨a, b⟩
        dsimp at hx1 hx2
        have eq1 : Localization.mk a b = Localization.mk 1 b * Localization.mk a 1 := by
          rw [Localization.mk_mul]; simp
        have hx3 : Localization.mk a 1 ∈ q.asIdeal := by
          rw [eq1] at hx1
          refine q.isPrime.mem_or_mem hx1 |>.resolve_left ?_
          intro r
          refine q.isPrime.1 (Ideal.eq_top_iff_one _ |>.mpr ?_)
          have eq2 : (Localization.mk 1 b : Localization.AtPrime i.asIdeal) *
            (Localization.mk b 1 : Localization.AtPrime i.asIdeal) =
            (1 : Localization.AtPrime i.asIdeal) := by rw [Localization.mk_mul]; simpa using Localization.mk_self b
          rw [← eq2]
          exact q.asIdeal.mul_mem_right _ r
        refine Set.not_subset.mpr ⟨a, ?_, ?_⟩ <;>
        simp only [SetLike.mem_coe, Ideal.mem_comap]
        · exact hx3
        · rw [eq1] at hx2
          have := p.isPrime.mul_mem_iff_mem_or_mem.not.mp hx2
          push_neg at this
          exact this.2

      rw [dim0.out] at this
      refine le_antisymm this krullDim_nonneg
    haveI : Fintype (PrimeSpectrum R) := by exact instFintypePrimeSpectrum_dimensionTheory R
    refine isArtinianRing_of_ringEquiv (e := equivProdLocalization.symm)

end IsNoetherianRing
