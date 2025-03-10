/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Ideal.Prod

/-!
# Product of Artinian rings is Artinian
-/

lemma isArtinianRing_of_ringEquiv {R} [Ring R] {S} [Ring S] (e : R ≃+* S) [IsArtinianRing R] :
    IsArtinianRing S :=
  Function.Surjective.isArtinianRing (hf := e.surjective)

instance isArtinianRing_prod {R} [Ring R] {S} [Ring S]
    [hR : IsArtinianRing R] [hS : IsArtinianRing S] : IsArtinianRing (R × S) := by
  change IsArtinian _ _ at hR hS ⊢
  rw [← monotone_stabilizes_iff_artinian] at hR hS ⊢
  intro f
  let fR : ℕ →o (Ideal R)ᵒᵈ :=
  { toFun := fun n ↦ Ideal.idealProdEquiv (f n) |>.1
    monotone' := by
      intros m n hmn x hx
      exact Ideal.map_mono (f.monotone hmn) hx }
  let fS : ℕ →o (Ideal S)ᵒᵈ :=
  { toFun := fun n ↦ Ideal.idealProdEquiv (f n) |>.2
    monotone' := by
      intros m n hmn x hx
      exact Ideal.map_mono (f.monotone hmn) hx }
  obtain ⟨nR, hR⟩ := hR fR
  obtain ⟨nS, hS⟩ := hS fS
  refine ⟨nR.max nS, fun m hm ↦ ?_⟩
  apply_fun Ideal.idealProdEquiv
  ext1
  · change fR _ = fR _
    simp only [max_le_iff] at hm
    rw [← hR (nR.max nS), ← hR m] <;>
    linarith [hm.1, hm.2, Nat.le_max_left nR nS]
  · change fS _ = fS _
    simp only [max_le_iff] at hm
    rw [← hS (nR.max nS), ← hS m] <;>
    linarith [hm.1, hm.2, Nat.le_max_right nR nS]

instance isArtinianRing_pi {ι : Type*} [Finite ι] (R : ι → Type*)
    [∀ i, Ring (R i)] [∀ i, IsArtinianRing (R i)] :
    IsArtinianRing (∀ i, R i) := by
  revert R
  apply Finite.induction_empty_option _ _ _ ι
  · intro α β e hα R _ _
    refine isArtinianRing_of_ringEquiv
      (?_ : (∀ (i : α), R (e i)) ≃+* ∀ (i : β), R i)
    · refine' { Equiv.piCongrLeft R e with .. } <;>
      · intros x y
        ext i
        have eq1 : i = e (e.symm i) := e.apply_symm_apply i |>.symm
        simp only [Equiv.toFun_as_coe, Pi.mul_apply, Pi.add_apply]
        rw [eq1, Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply,
          Equiv.piCongrLeft_apply_apply]
        rfl
  · intros
    infer_instance
  · intro α _ ih R _ _
    refine isArtinianRing_of_ringEquiv (⟨Equiv.piOptionEquivProd (β := R), ?_, ?_⟩ :
      ((a : Option α) → R a) ≃+* R none × ((a : α) → R (some a))).symm <;>
    aesop
