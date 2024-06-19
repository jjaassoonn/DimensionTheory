/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts

/-!
# A trivial lemma for sheaf condition in terms of equalizer products
-/

universe v' v u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasProducts.{v'} C]
variable {X : TopCat.{v'}} (F : Presheaf C X) {ι : Type v'} (U : ι → Opens X)

open Presheaf.SheafConditionEqualizerProducts in
lemma Sheaf.sections_on_disjoint_opens_iso_product (F : Sheaf.{v', v, u} C X)
    {ι : Type v'} (U : ι → Opens X) (hU : ∀ i j, i ≠ j → U i ⊓ U j = ⊥) :
    Nonempty <| F.presheaf.obj (op <| iSup U) ≅ ∏ᶜ fun i : ι ↦ F.presheaf.obj (op <| U i) := by
  refine (F.presheaf.isSheaf_iff_isSheafEqualizerProducts |>.mp F.2 U).map
    fun (H : IsLimit <| Fork.ofι _ _) ↦ @CategoryTheory.asIso (f := _) <|
      Limits.isIso_limit_cone_parallelPair_of_eq ?_ H
  delta leftRes rightRes; congr; ext ⟨i, j⟩
  by_cases eq1 : i = j
  · subst eq1; rfl
  · exact (F.isTerminalOfEqEmpty (hU _ _ eq1)).hom_ext _ _

end TopCat
