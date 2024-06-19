/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/

import Mathlib.Algebra.Module.GradedModule

/-!
# Projection maps of internally graded modules
-/

open DirectSum

variable {ιA ιM R A M σ σ' : Type*}
variable [AddMonoid ιA] [AddAction ιA ιM] [CommSemiring R] [Semiring A] [Algebra R A]
variable (𝓐 : ιA → σ') [SetLike σ' A]
variable (𝓜 : ιM → σ)

variable [AddCommMonoid M] [Module A M] [SetLike σ M] [AddSubmonoidClass σ' A]
  [AddSubmonoidClass σ M] [SetLike.GradedMonoid 𝓐] [SetLike.GradedSMul 𝓐 𝓜]

namespace GradedModule


/--
The projection map of an internally graded module.
-/
@[simps]
def proj [DecidableEq ιM] [Decomposition 𝓜]  (i : ιM) : M →+ M where
  toFun m := decompose 𝓜 m i
  map_zero' := by simp
  map_add' := by simp

/--
For each `a : M`, `GradedModule.homogeneousComponents ℳ a` is the collection of the
homogeneous components of `a`, which is a finite subset of `M`.
-/
def homogeneousComponents [DecidableEq ιM] [Decomposition 𝓜] [DecidableEq M] (a : M) : Finset M :=
    (decompose 𝓜 a).support.image (decompose 𝓜 a ·)

lemma homogeneous_of_mem_homogeneousComponents [DecidableEq ιM] [Decomposition 𝓜] [DecidableEq M]
    {a b : M} (hb : b ∈ homogeneousComponents 𝓜 a) : SetLike.Homogeneous 𝓜 b := by
  change b ∈ (decompose 𝓜 a).support.image _ at hb
  aesop

section same_indexing_set

variable {σA σM : Type*} (𝒜 : ℕ → σA) (ℳ : ℕ → σM)
variable [AddCommMonoid M] [Module A M] [SetLike σA A] [SetLike σM M]
variable [AddSubmonoidClass σA A] [AddSubmonoidClass σM M]
variable [GradedRing 𝒜] [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]


lemma proj_smul_mem_right {i j : ℕ} (a : A) (m : M) (hm : m ∈ ℳ i) :
    GradedModule.proj ℳ j (a • m) =
    if i ≤ j
    then GradedRing.proj 𝒜 (j - i) a • m
    else 0 := by
  classical
  letI := isModule 𝒜 ℳ
  rw [← DirectSum.sum_support_decompose ℳ (a • m), map_sum, Finset.sum_eq_single j,
    proj_apply, decompose_of_mem_same (hx := SetLike.coe_mem _)]
  pick_goal 2
  · intro n _ hne; rw [proj_apply, decompose_of_mem_ne (hx := SetLike.coe_mem _) hne]
  pick_goal 2
  · intro hj
    simpa using hj

  have eq0 : decompose ℳ (a • m) = a • decompose ℳ m := (linearEquiv 𝒜 ℳ).1.map_smul a m
  rw [eq0]
  show ((DirectSum.decompose 𝒜 a • DirectSum.decompose ℳ m) j : M) = _
  conv_lhs => rw [← DirectSum.sum_support_decompose ℳ m,
    ← DirectSum.sum_support_decompose 𝒜 a, DirectSum.decompose_sum,
    Finset.sum_smul, DirectSum.decompose_sum]
  simp_rw [Finset.smul_sum]
  have eq1 (k : ℕ) :
    ∑ j in (decompose ℳ m).support,
      (decompose 𝒜 (decompose 𝒜 a k)) • decompose ℳ (decompose ℳ m j) =
    decompose 𝒜 (decompose 𝒜 a k) • decompose ℳ m := by
    rw [Finset.sum_eq_single i, decompose_of_mem_same ℳ hm]
    · intro j _ hne
      rw [decompose_of_mem_ne ℳ hm hne.symm, decompose_zero, smul_zero]
    · intro hi
      simp only [DFinsupp.mem_support_toFun, ne_eq, not_not] at hi
      simp only [decompose_coe, hi, ZeroMemClass.coe_zero, decompose_zero, smul_zero]
  simp_rw [eq1]
  lift m to ℳ i using hm
  simp_rw [decompose_coe, DirectSum.Gmodule.of_smul_of, vadd_eq_add]

  split_ifs with h
  · rw [DFinsupp.finset_sum_apply, Finset.sum_eq_single (j - i), DirectSum.coe_of_apply,
      if_pos (Nat.sub_add_cancel h)]
    · rfl
    · intro n _ hn2
      rw [of_eq_of_ne]
      contrapose! hn2
      exact Nat.sub_eq_of_eq_add hn2.symm |>.symm

    · intro H
      ext
      simp only [DFinsupp.mem_support_toFun, ne_eq, not_not] at H
      rw [H, Gmodule.zero_smul, coe_of_apply, if_pos (Nat.sub_add_cancel h)]
      rfl

  · rw [DFinsupp.finset_sum_apply]
    push_cast
    simp_rw [coe_of_apply]
    apply Finset.sum_eq_zero
    intro k _
    simp only [not_le] at h
    rw [if_neg]
    · rfl
    · linarith

lemma proj_smul_mem_left {i j : ℕ} (a : A) (m : M) (ha : a ∈ 𝒜 i) :
    GradedModule.proj ℳ j (a • m) =
    if i ≤ j
    then a • GradedModule.proj ℳ (j - i) m
    else 0 := by
  by_cases a_ne_zero : a = 0
  · subst a_ne_zero
    rw [zero_smul, zero_smul, map_zero, ite_self]

  classical
  letI := isModule 𝒜 ℳ
  rw [← DirectSum.sum_support_decompose ℳ (a • m), map_sum, Finset.sum_eq_single j,
    proj_apply, decompose_of_mem_same (hx := SetLike.coe_mem _)]
  pick_goal 2
  · intro n _ hne; rw [proj_apply, decompose_of_mem_ne (hx := SetLike.coe_mem _) hne]
  pick_goal 2
  · intro hj
    simpa using hj

  have eq0 : decompose ℳ (a • m) = a • decompose ℳ m := (linearEquiv 𝒜 ℳ).1.map_smul a m
  rw [eq0]
  show ((DirectSum.decompose 𝒜 a • DirectSum.decompose ℳ m) j : M) = _
  conv_lhs => rw [← DirectSum.sum_support_decompose ℳ m,
    ← DirectSum.sum_support_decompose 𝒜 a, DirectSum.decompose_sum,
    Finset.sum_smul, DirectSum.decompose_sum]

  simp_rw [Finset.smul_sum]

  rw [calc _
    _ = ((∑ i in (decompose 𝒜 a).support, ∑ j in (decompose ℳ m).support,
          decompose 𝒜 (decompose 𝒜 a i) • decompose ℳ (decompose ℳ m j)) j : M) := rfl
    _ = ((∑ ik in (decompose 𝒜 a).support ×ˢ (decompose ℳ m).support,
          decompose 𝒜 (decompose 𝒜 a ik.1) • decompose ℳ (decompose ℳ m ik.2)) j : M) := by
        rw [Finset.sum_product]
    _ = (∑ ik in (decompose 𝒜 a).support ×ˢ (decompose ℳ m).support,
          ((decompose 𝒜 (decompose 𝒜 a ik.1) • decompose ℳ (decompose ℳ m ik.2)) j) : ℳ j) := by
        congr 1
        exact DFinsupp.finset_sum_apply _ _ _
    _ = ∑ ik in (decompose 𝒜 a).support ×ˢ (decompose ℳ m).support,
          ((decompose 𝒜 (decompose 𝒜 a ik.1) • decompose ℳ (decompose ℳ m ik.2)) j : M) := by
        norm_cast
    _ = ∑ ik in (decompose 𝒜 a).support ×ˢ (decompose ℳ m).support,
          ((of (fun i ↦ ℳ i) (ik.1 + ik.2)
            ⟨(decompose 𝒜 a ik.1 : A) • (decompose ℳ m ik.2 : M), _⟩) j : M) := by
        refine Finset.sum_congr rfl fun ik _ ↦ ?_
        simp only [decompose_coe, Gmodule.smul_def, Gmodule.smulAddMonoidHom_apply_of_of,
          vadd_eq_add, SetLike.coe_eq_coe]
        rfl
    _ = ∑ ik in (decompose 𝒜 a).support ×ˢ (decompose ℳ m).support,
          if ik.1 + ik.2 = j
          then (decompose 𝒜 a ik.1 : A) • (decompose ℳ m ik.2 : M)
          else 0 := by
        refine Finset.sum_congr rfl fun ik _ ↦ ?_
        rw [DirectSum.coe_of_apply]
        split_ifs <;> rfl, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  by_cases hi : i ∈ (decompose 𝒜 a).support
  pick_goal 2
  · simp only [DFinsupp.mem_support_toFun, ne_eq, Subtype.ext_iff, decompose_of_mem_same 𝒜 ha,
      ZeroMemClass.coe_zero, not_not] at hi
    subst hi
    simp_rw [decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero, zero_smul]
    rw [ite_self, Finset.sum_const_zero]

  by_cases hj : j - i ∈ (decompose ℳ m).support
  pick_goal 2
  · simp only [DFinsupp.mem_support_toFun, ne_eq, not_not, Subtype.ext_iff,
      ZeroMemClass.coe_zero] at hj
    rw [proj_apply, hj, smul_zero, ite_self]
    convert Finset.sum_empty
    rw [Finset.eq_empty_iff_forall_not_mem]
    rintro ⟨i', j'⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, DFinsupp.mem_support_toFun, ne_eq] at h
    have hii' : i = i' := by
      by_contra hii'
      exact h.1.1 <| Subtype.ext <| DirectSum.decompose_of_mem_ne 𝒜 ha hii'
    subst hii'
    refine h.1.2 ?_
    by_cases ineq : i ≤ j
    · have hjj' : j' = j - i := by
        symm; rw [Nat.sub_eq_iff_eq_add ineq, add_comm, h.2]
      subst hjj'
      exact Subtype.ext hj
    · simp only [not_le] at ineq
      exfalso
      linarith only [(h.2 : i + j' = j), ineq]

  split_ifs with ineq
  · trans ∑ ik in {(i, j - i)}, (decompose 𝒜 a ik.1 : A) • (decompose ℳ m ik.2 : M)
    · refine Finset.sum_congr ?_ fun _ _ ↦ rfl
      rw [Finset.eq_singleton_iff_unique_mem, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨⟨hi, hj⟩, show i + (j - i) = j from Nat.add_sub_of_le ineq⟩, ?_⟩
      rintro ⟨i', j'⟩ h
      simp only [Finset.mem_filter, Finset.mem_product, DFinsupp.mem_support_toFun, ne_eq] at h
      have hii' : i = i' := by
        by_contra hii'
        exact h.1.1 <| Subtype.ext <| DirectSum.decompose_of_mem_ne 𝒜 ha hii'
      subst hii'
      have hjj' : j' = j - i := by
        symm; rw [Nat.sub_eq_iff_eq_add ineq, add_comm, h.2]
      subst hjj'
      rfl
    · rw [Finset.sum_singleton, DirectSum.decompose_of_mem_same 𝒜 ha, proj_apply]
  · convert Finset.sum_empty
    rw [Finset.eq_empty_iff_forall_not_mem]
    rintro ⟨i', j'⟩ h
    simp only [Finset.mem_filter, Finset.mem_product, DFinsupp.mem_support_toFun, ne_eq] at h
    simp only [not_le] at ineq
    have hii' : i = i' := by
      by_contra hii'; exact h.1.1 <| Subtype.ext <| DirectSum.decompose_of_mem_ne 𝒜 ha hii'
    subst hii'
    linarith only [(h.2 : i + j' = j), ineq]

end same_indexing_set

end GradedModule
