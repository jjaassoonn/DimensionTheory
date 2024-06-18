/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.Algebra.PUnitInstances
import Mathlib.Algebra.Module.Equiv

/-!
If a module has only one element, then it is isomorphic to the trivial module.

-/

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
