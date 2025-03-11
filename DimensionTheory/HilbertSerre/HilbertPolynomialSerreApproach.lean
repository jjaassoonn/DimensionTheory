import DimensionTheory.HilbertSerre.Theorem
import DimensionTheory.Module.Length
import DimensionTheory.Module.FGModuleCat.Length
import DimensionTheory.Module.Graded.Subgrading
import DimensionTheory.PolynomialLikeFunction
import DimensionTheory.Module.Graded.RingHom
import DimensionTheory.HilbertSerre.Polynomial

import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.MvPolynomial.Homogeneous


suppress_compilation

universe u
variable {A M : Type u}
variable [CommRing A] [AddCommGroup M] [Module A M]
variable [finite_module : Module.Finite A M]
variable (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] [IsArtinianRing (𝒜 0)]
variable (ℳ : ℕ → AddSubgroup M) [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]

variable (S : generatingSetOverBaseRing 𝒜) (S_deg : ∀ i : S.toFinset, S.deg i.2 = 1)



namespace generatingSetOverBaseRing

def poly : Type u := MvPolynomial S.toFinset (𝒜 0)

instance : AddCommGroup S.poly := inferInstanceAs <| AddCommGroup <| MvPolynomial S.toFinset (𝒜 0)

instance : Module (𝒜 0) S.poly := inferInstanceAs <| Module (𝒜 0) <| MvPolynomial S.toFinset (𝒜 0)

instance : CommRing (S.poly) := inferInstanceAs <| CommRing <| MvPolynomial S.toFinset (𝒜 0)

instance : Algebra (𝒜 0) S.poly := inferInstanceAs <| Algebra (𝒜 0) <| MvPolynomial S.toFinset (𝒜 0)

instance : Algebra.FiniteType (𝒜 0) S.poly := Algebra.FiniteType.mvPolynomial _ _

instance : Algebra.FiniteType (𝒜 0) A where
  out := ⟨S.toFinset, S.span_eq⟩

variable {𝒜}

unif_hint where
  ⊢ S.poly ≟ MvPolynomial S.toFinset (𝒜 0)

abbrev grading (i : ℕ) : Submodule (𝒜 0) S.poly :=
  MvPolynomial.homogeneousSubmodule S.toFinset (𝒜 0) i

instance : GradedAlgebra (A := S.poly) S.grading := MvPolynomial.gradedAlgebra

abbrev aeval : GradedRingHom S.grading 𝒜 where
  __ : S.poly →ₐ[𝒜 0] A := MvPolynomial.aeval Subtype.val
  map_mem' := by
    intro i p hp
    simp only [grading, AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
      MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe] at hp ⊢
    rw [MvPolynomial.mem_homogeneousSubmodule] at hp
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
    refine AddSubgroup.sum_mem _ fun x _ => ?_
    by_cases coeff_eq : MvPolynomial.coeff x p = 0
    · rw [coeff_eq]
      simp only [map_zero, zero_mul]
      exact AddSubgroup.zero_mem _
    have := @hp x coeff_eq
    simp only [Finsupp.weight, Finsupp.linearCombination, Pi.one_apply,
      LinearMap.toAddMonoidHom_coe, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe,
      id_eq, smul_eq_mul, mul_one, Finsupp.sum] at this
    rw [← this]
    rw [show ∑ j ∈ x.support, x j = 0 + ∑ j ∈ x.support, x j by rw [zero_add]]
    apply SetLike.mul_mem_graded
    · exact SetLike.coe_mem _
    · rw [← Finset.prod_to_list, ← Finset.sum_to_list]
      apply SetLike.list_prod_map_mem_graded
      intro j hj
      simp only [Finset.mem_toList, Finsupp.mem_support_iff, ne_eq] at hj ⊢
      have : (j : A) ∈ 𝒜 1 := by
        have := S.mem_deg j.2
        rwa [S_deg] at this
      have := SetLike.pow_mem_graded (x j) this
      simp only [smul_eq_mul, mul_one] at this
      exact this

omit [IsArtinianRing ↥(𝒜 0)] in
lemma aeval_apply (p : S.poly) : S.aeval S_deg p = MvPolynomial.aeval Subtype.val p := rfl

def quotiented : HomogeneousIdeal S.grading := (S.aeval S_deg).ker


omit [IsArtinianRing (𝒜 0)] in
lemma surjective_aeval : Function.Surjective (S.aeval S_deg) := fun a => by
  have : a ∈ (⊤ : Subalgebra (𝒜 0) A) := ⟨⟩
  rw [← S.span_eq] at this
  refine Algebra.adjoin_induction (hx := this) ?_ ?_ ?_ ?_
  · rintro s hs
    use MvPolynomial.X ⟨s, hs⟩
    simp only [aeval_apply, MvPolynomial.aeval_X]
  · intro r
    use MvPolynomial.C r
    simp only [aeval_apply, MvPolynomial.algHom_C]
  · rintro _ _ _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    use (x + y)
    simp only [map_add, aeval_apply]
  · rintro _ _ _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    use (x * y)
    simp only [map_mul, aeval_apply]

def quotientEquiv :
    (S.poly ⧸ (S.quotiented S_deg).toIdeal) ≃ₐ[𝒜 0] A :=
  Ideal.quotientKerAlgEquivOfSurjective <| S.surjective_aeval S_deg

instance : IsNoetherianRing (𝒜 0) := inferInstance

instance : IsNoetherianRing S.poly :=
  inferInstanceAs <| IsNoetherianRing <| MvPolynomial S.toFinset (𝒜 0)

include S_deg in
theorem noetherian : IsNoetherianRing A :=
  isNoetherianRing_of_ringEquiv _ (quotientEquiv S S_deg).toRingEquiv

end generatingSetOverBaseRing

variable [IsNoetherianRing A]

def hilbertχ : ℤ → ℤ
| .ofNat i => (FGModuleCat.of (𝒜 0) (ℳ i)).length
| .negSucc _ => 0

instance : Function.PolynomialLike (hilbertχ 𝒜 ℳ) := by
  constructor
  use HilbertSerre.hilbertPolynomial 𝒜 ℳ (FGModuleCat.lengthAdditiveFunction (𝒜 0)) S
  simp only [Filter.eventually_atTop, ge_iff_le]
  use (HilbertSerre.numeratorPolynomial 𝒜 ℳ (FGModuleCat.lengthAdditiveFunction ↥(𝒜 0)) S).natDegree + 1
  intro n hn
  have hn' : 0 ≤ n := le_trans (by omega) hn
  lift n to ℕ using hn'
  norm_cast at hn
  have := HilbertSerre.AdditiveFunction_eq_hilbertPolynomial_eval 𝒜 ℳ
    (FGModuleCat.lengthAdditiveFunction (𝒜 0)) S S_deg n hn
  simp only [hilbertχ, Int.cast_natCast]
  exact this

#check hilbert_serre 𝒜 ℳ (FGModuleCat.lengthAdditiveFunction (𝒜 0))
