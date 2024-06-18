import Mathlib.RingTheory.SimpleModule

namespace IsSimpleModule

variable {R : Type*} [Ring R]

/-- if `X` is isomorphic to a submodule of a simple module, then either `X` is trivial or it is that
  simple module-/
noncomputable def equiv_punit_sum_equiv_of_equiv_submodule
    {m : Type*} [AddCommGroup m] [Module R m] [hm : IsSimpleModule R m]
    (X : Type*) [AddCommGroup X] [Module R X] (x : Submodule R m)
    (e : X ≃ₗ[R] x) : (X ≃ₗ[R] (PUnit : Type*)) ⊕ (X ≃ₗ[R] m) := by
  classical
  refine Or.by_cases (hm.2 x) (λ EQ ↦ Sum.inl {
    toFun := λ _ ↦ PUnit.unit
    map_add' := λ _ _ ↦ rfl
    map_smul' := λ _ _ ↦ rfl
    invFun := λ _ ↦ 0
    left_inv := ?_
    right_inv := λ _ ↦ rfl
  }) $ λ EQ ↦ Sum.inr {
    toFun := Subtype.val ∘ e
    map_add' := ?_
    map_smul' := ?_
    invFun := e.symm ∘ λ x ↦ ⟨x, EQ.symm ▸ ⟨⟩⟩
    left_inv := ?_
    right_inv := ?_
  }
  · subst EQ
    exact λ _ ↦ Subsingleton.elim (h := Equiv.subsingleton e.toEquiv) _ _
  all_goals
  · intro; aesop

/-- if `X` is isomorphic to a submodule of a simple module, then either `X` is trivial or it is that
  simple module, a version of `Prop`-/
lemma equiv_punit_sum_equiv_of_equiv_submodule'
    {m : Type*} [AddCommGroup m] [Module R m] [hm : IsSimpleModule R m]
    (X : Type*) [AddCommGroup X] [Module R X] (x : Submodule R m)
    (e : X ≃ₗ[R] x) : (Nonempty $ X ≃ₗ[R] (PUnit : Type*)) ∨ (Nonempty $ X ≃ₗ[R] m) := by
  classical
  exact (equiv_punit_sum_equiv_of_equiv_submodule X x e).elim (Or.inl ∘ Nonempty.intro)
    (Or.inr ∘ Nonempty.intro)

end IsSimpleModule
