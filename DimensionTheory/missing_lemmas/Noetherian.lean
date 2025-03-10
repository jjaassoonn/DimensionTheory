/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import DimensionTheory.missing_lemmas.Ideal

import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Localization.Ideal

/-!
# some missing lemmas about noetherian rings
-/

lemma IsNoetherianRing.Pi {ι : Type*} [Fintype ι] (f : ι → Type*)
    [(i : ι) → CommRing (f i)] [noetherian : (i : ι) → IsNoetherianRing (f i)] :
    IsNoetherianRing ((i : ι) → f i) := by
  classical
  simp_rw [isNoetherianRing_iff_ideal_fg] at noetherian ⊢
  intro I
  apply Ideal.Pi_fg_of_unPi_fg
  intro i
  exact noetherian i _

lemma IsNoetherianRing.Localization
    {R : Type*} [CommRing R] [noeth : IsNoetherianRing R] (s : Submonoid R)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization s S] :
    IsNoetherianRing S := by
  change IsNoetherian _ _ at noeth ⊢
  rw [← monotone_stabilizes_iff_noetherian] at noeth ⊢
  intro f
  obtain ⟨n, hn⟩ := noeth <| OrderHom.comp (IsLocalization.orderEmbedding s S) f
  refine ⟨n, fun m hm ↦ ?_⟩
  specialize hn m hm
  simpa using hn
