import Mathlib.Algebra.PUnitInstances
import Mathlib.LinearAlgebra.Basic

namespace PUnit

/--
If `M` is the trivial `R`-module, then it is isomorphic to `*`
-/
def linearEquivOfUnique (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
    [uniq : Unique M] : M ≃ₗ[R] PUnit where
  toFun _ := ⟨⟩
  map_add' := by aesop
  map_smul' := by aesop
  invFun _ := default
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := rfl

end PUnit
