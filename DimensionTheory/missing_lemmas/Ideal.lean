/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.RingTheory.Ideal.Basic

/-!
# Some missing lemmas on ideals
-/

open BigOperators

theorem Ideal.IsPrime.prod_mem_iff_exists_mem'
    {R : Type*} [CommRing R] {I : Ideal R} (hI : I.IsPrime)
    {ι : Type*} [DecidableEq ι] (f : ι → R) (s : Finset ι) :
    (∏ i ∈ s, f i) ∈ I ↔ ∃ i ∈ s, f i ∈ I := by
  induction s using Finset.induction_on with
  | empty => simpa [Ideal.ne_top_iff_one] using hI.ne_top
  | @insert i s hi ih =>
    simp [Finset.prod_insert hi, Ideal.IsPrime.mul_mem_iff_mem_or_mem, ih]
