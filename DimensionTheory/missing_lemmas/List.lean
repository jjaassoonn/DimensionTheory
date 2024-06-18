/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.Data.List.Dedup

/-!

# Some missing lemmas about lists

especially about `dedup` and `nodup`

-/

namespace List

variable {α β : Type*} [DecidableEq α]

lemma map_ne_nil_of_ne_nil (l : List α) (h : l ≠ List.nil)
    (f : α → β) : l.map f ≠ List.nil := by
  cases l with | nil => ?_ | cons x l => ?_
  · cases h rfl
  · dsimp; exact List.cons_ne_nil _ _

lemma dedup_length_lt_of_not_nodup (l : List α) (h : ¬ l.Nodup) :
    l.dedup.length < l.length := by
  contrapose! h
  have h' := _root_.le_antisymm h (List.Sublist.length_le (List.dedup_sublist l))
  rw [← List.dedup_eq_self]
  exact List.Sublist.eq_of_length (List.dedup_sublist _) h'.symm

lemma dedup_ne_nil_of_ne_nil (l : List α) (h : l ≠ List.nil) :
    l.dedup ≠ List.nil := by
  contrapose! h
  rw [List.eq_nil_iff_forall_not_mem] at h ⊢
  intros a
  rw [← List.mem_dedup]
  exact h a

lemma Nodup.get_not_mem_take {α : Type*} {l : List α}
    (hl : l.Nodup) (n : ℕ) (hn : n < l.length) : l.get ⟨n, hn⟩ ∉ l.take n := by
  revert n
  induction' l with a l ih
  · simp
  · intro n hn
    induction' n with n
    · simp
    · simp only [List.length_cons, List.get_cons_succ, List.take_cons_succ, Bool.not_eq_true,
        List.mem_cons, not_or] at hn ⊢
      refine ⟨?_, ih (List.nodup_cons.mp hl).2 _ <| Nat.succ_lt_succ_iff.mp hn⟩
      rintro eq1
      have := hl.get_inj_iff (i := ⟨0,  by simp only [List.length_cons, Nat.zero_lt_succ]⟩)
        (j := ⟨n.succ, by rw [List.length_cons]; exact hn⟩)
      simp only [List.length_cons, Fin.zero_eta, List.get_cons_zero, ← eq1, List.get_cons_succ,
        true_iff] at this
      cases this

end List
