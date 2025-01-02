import DimensionTheory.Module.Length
import DimensionTheory.Module.FGModuleCat.Abelian
import DimensionTheory.RingTheory.ArtinianAndNoetherian
import DimensionTheory.HilbertSerre.AdditiveFunction

suppress_compilation

open CategoryTheory

namespace FGModuleCat

universe u

variable {R : Type u} [CommRing R] [IsArtinianRing R]

variable (M : FGModuleCat R)

def length : ℕ := moduleLength R M |>.get!

lemma length_eq_moduleLength : M.length = moduleLength R M := by
  apply Option.some_get!
  delta moduleLength
  split_ifs with h
  · rfl
  exfalso
  apply h
  infer_instance

variable (R) in
def lengthAdditiveFunction : FGModuleCat R ⟹+ ℤ where
  toFun M := M.length
  additive s hs := by
    dsimp
    norm_cast
    apply_fun WithTop.some using WithTop.coe_injective
    push_cast
    -- have := s.X₂.length_eq_moduleLength
    -- refine Eq.trans ?_ this.symm
    have eq1 := s.X₁.length_eq_moduleLength
    have eq2 := s.X₂.length_eq_moduleLength
    have eq3 := s.X₃.length_eq_moduleLength
    refine Eq.trans congr($eq1 + $eq3) <| Eq.symm <| eq2.trans <|
      moduleLength.eq_length_submodule_add_length_quotient (LinearMap.ker s.g) |>.trans ?_
    congr 1
    · apply moduleLength_congr
      rw [← FGModuleCat.exact_iff s |>.1 hs.1]
      have inj := hs.2
      rw [ConcreteCategory.mono_iff_injective_of_preservesPullback] at inj
      exact LinearEquiv.ofInjective s.f inj |>.symm

    · apply moduleLength_congr
      refine LinearMap.quotKerEquivRange s.g ≪≫ₗ ?_
      have surj : Function.Surjective s.g := by
        rw [← FGModuleCat.epi_iff_surjective]
        exact hs.3
      rw [LinearMap.range_eq_top |>.2 surj]
      exact Submodule.topEquiv

end FGModuleCat
