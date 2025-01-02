import DimensionTheory.Module.Graded.Subgrading

section

variable {A B : Type*} [Ring A] [Ring B]
variable {ι : Type*} [DecidableEq ι] [AddMonoid ι]
variable {σA σB : Type*} [SetLike σA A] [SetLike σB B] [AddSubgroupClass σA A] [AddSubgroupClass σB B]
variable (𝒜 : ι → σA) [GradedRing 𝒜]
variable (ℬ : ι → σB) [GradedRing ℬ]

structure GradedRingHom extends RingHom A B where
  map_mem' : ∀ {i} {x : A}, x ∈ 𝒜 i → toFun x ∈ ℬ i

namespace GradedRingHom

instance : FunLike (GradedRingHom 𝒜 ℬ) A B where
  coe f := f.toFun
  coe_injective' := by
    rintro ⟨f, _⟩ ⟨g, _⟩ h
    simp only [mk.injEq] at h ⊢
    ext x
    exact congr_fun h x

instance : RingHomClass (GradedRingHom 𝒜 ℬ) A B where
  map_mul f := f.toRingHom.map_mul
  map_one f := f.toRingHom.map_one
  map_add f := f.toRingHom.map_add
  map_zero f := f.toRingHom.map_zero

open DirectSum

variable {𝒜 ℬ}
def directSum (f : GradedRingHom 𝒜 ℬ) : (⨁ i, 𝒜 i) →+* (⨁ i, ℬ i) :=
  RingHom.comp (DirectSum.decomposeRingEquiv ℬ) <| f.comp (DirectSum.decomposeRingEquiv 𝒜).symm

@[simp]
lemma directSum_apply_of (f : GradedRingHom 𝒜 ℬ) (i : ι) (x : 𝒜 i) :
    f.directSum (of _ i x) = of _ i ⟨f x, f.map_mem' x.2⟩ := by
  apply_fun (DirectSum.decomposeRingEquiv ℬ).symm
  simp only [decomposeRingEquiv, AddEquiv.toEquiv_eq_coe, AddEquiv.toEquiv_symm,
    RingEquiv.symm_symm, directSum, RingHom.coe_comp, RingHom.coe_coe, RingEquiv.coe_mk,
    AddEquiv.coe_toEquiv_symm, Function.comp_apply, decomposeAddEquiv_symm_apply, decompose_symm_of,
    RingEquiv.apply_symm_apply]
  rfl

/-
A   ---f---> B
|           |
⨁ᵢ 𝒜 i ->  ⨁ᵢ ℬ i

-/
lemma comm_sq1 (f : GradedRingHom 𝒜 ℬ) :
    (decomposeRingEquiv ℬ).toRingHom.comp f =
    RingHom.comp f.directSum (decomposeRingEquiv 𝒜).toRingHom := by
  simp only [RingEquiv.toRingHom_eq_coe, directSum, RingHom.comp_assoc, RingEquiv.symm_comp,
    RingHomCompTriple.comp_eq]
  rfl

lemma comm_sq1_apply (f : GradedRingHom 𝒜 ℬ) (x : A) :
    decomposeRingEquiv ℬ (f x) = f.directSum (decomposeRingEquiv 𝒜 x) :=
  congr($f.comm_sq1 x)

lemma decompose_apply (f : GradedRingHom 𝒜 ℬ) (x : A) :
    decompose ℬ (f x) = f.directSum (decompose 𝒜 x) :=
  f.comm_sq1_apply x

example (x : A) (f : GradedRingHom 𝒜 ℬ) :
    decompose ℬ (f x) = f.directSum (decompose 𝒜 x) := by
  rw [decompose_apply]

lemma apply_decompose (f : GradedRingHom 𝒜 ℬ) (x : A) (i : ι) :
    f (decompose 𝒜 x i) = f.directSum (decompose 𝒜 x) i := by
  classical
  have := congr(decomposeAddEquiv ℬ (f $(sum_support_decompose 𝒜 x)))
  rw [map_sum, map_sum] at this
  have := congr($this i)
  simp only [decomposeAddEquiv_apply] at this
  apply_fun decompose ℬ
  rw [decompose_apply, decompose_coe, directSum_apply_of, decompose_coe]
  congr
  simp only [DFinsupp.toFun_eq_coe]
  rw [← decompose_apply]
  rw [← this]
  erw [DFinsupp.finset_sum_apply]
  rw [AddSubmonoidClass.coe_finset_sum]
  symm
  simp_rw [decompose_apply]
  simp only [decompose_coe, directSum_apply_of, coe_of_apply]
  calc _
    _ = ∑ j ∈ (decompose 𝒜 x).support, if j = i then f (decompose 𝒜 x i) else 0 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      aesop
  simp only [Finset.sum_ite_eq', DFinsupp.mem_support_toFun, ne_eq, ite_not, ite_eq_right_iff]
  intro h
  simp [h]

def ker (f : GradedRingHom 𝒜 ℬ) : HomogeneousIdeal 𝒜 where
  __ := RingHom.ker f
  is_homogeneous' := by
    classical
    intro i x hx
    simp only [RingHom.mem_ker] at hx ⊢
    rw [apply_decompose]
    simp only [ZeroMemClass.coe_eq_zero]
    rw [← decompose_apply, hx]
    simp only [decompose_zero, zero_apply]

end GradedRingHom

end

section

variable {R A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
variable {ι : Type*} [DecidableEq ι] [AddMonoid ι]
variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
variable (ℬ : ι → Submodule R B) [GradedAlgebra ℬ]


structure GradedAlgHom extends A →ₐ[R] B, GradedRingHom 𝒜 ℬ

end
