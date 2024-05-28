import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent

open Polynomial

variable (R : Type*) [DivisionRing R]
variable {ι : Type*} (B : ι → R[X])

lemma Polynomial.finset_linearIndependent_of_natDegree_distinct'
    (s : Finset (R[X]))
    (ne_zero : ∀ i, i ∈ s → i ≠ 0)
    (degree_distinct : ∀ (i j), i ∈ s → j ∈ s → i ≠ j → i.natDegree ≠ j.natDegree) :
    LinearIndependent R (ι := s) (fun i => i.1) := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    cases Finset.eq_empty_or_nonempty s with
    | inl eq =>
      rw [eq]
      exact linearIndependent_empty_type
    | inr s_ne =>
      let M : ℕ := s.image (fun i => i.natDegree) |>.max' (Finset.image_nonempty.mpr s_ne)
      have hM : M ∈ s.image (fun i => i.natDegree) := Finset.max'_mem _ _
      obtain ⟨p, hp1, hp2⟩ := Finset.mem_image.mp hM
      have s_eq : s = insert p (s.erase p) := sorry
      suffices LinearIndependent R (fun (i : (insert p (s.erase p) : Finset (R[X]))) => i.1) by
        convert this
      convert @linearIndependent_insert R R[X] _ _ _ (s.erase p) p sorry |>.mpr ?_
      · change _ ↔ _ ∈ (_ : Set R[X])
        simp only [Finset.mem_insert, Finset.mem_erase, ne_eq, Finset.coe_erase, Set.mem_diff,
          Finset.mem_coe, Set.mem_singleton_iff, Set.mem_setOf_eq]
        tauto
      · change _ ↔ _ ∈ (_ : Set R[X])
        simp only [Finset.mem_insert, Finset.mem_erase, ne_eq, Finset.coe_erase,
          Set.insert_diff_singleton, Set.mem_insert_iff, Finset.mem_coe]
        tauto
      constructor
      · have := ih (s.erase p) sorry sorry sorry
        convert this
      intro r
      sorry

lemma Polynomial.finset_linearIndependent_of_natDegree_distinct
    (s : Finset ι)
    (ne_zero : ∀ i, i ∈ s → B i ≠ 0)
    (degree_distinct : ∀ (i j), i ∈ s → j ∈ s → i ≠ j → (B i).natDegree ≠ (B j).natDegree) :
    LinearIndependent R (fun i : s ↦ B i) := by
  classical
  have := Polynomial.finset_linearIndependent_of_natDegree_distinct' R (s.image B)
    (by
      intro i hi
      simp only [Finset.mem_image] at hi
      rcases hi with ⟨i, hi, rfl⟩
      apply ne_zero _ hi)
    (by
      intro i j hi hj
      simp only [Finset.mem_image] at hi hj
      rcases hi with ⟨i, hi, rfl⟩
      rcases hj with ⟨j, hj, rfl⟩
      intro h

      apply degree_distinct _ _ hi hj
      rintro rfl
      simp at h)
  let e : s ≃ s.image B :=
  { toFun := fun x ↦ ⟨B x, Finset.mem_image_of_mem _ x.2⟩
    invFun := fun x ↦ ⟨Finset.mem_image.mp x.2 |>.choose,
      Finset.mem_image.mp x.2 |>.choose_spec.1⟩
    left_inv := by
      rintro ⟨x, hx⟩
      ext
      simp only
      generalize_proofs h
      specialize degree_distinct x h.choose hx h.choose_spec.1
      by_contra! h'
      specialize degree_distinct h'.symm
      rw [h.choose_spec.2] at degree_distinct
      simp at degree_distinct
    right_inv := by
      rintro ⟨x, hx⟩
      simp only [Finset.mem_image] at hx
      rcases hx with ⟨y, -, rfl⟩
      simp only [Subtype.mk.injEq]
      generalize_proofs h
      exact h.choose_spec.2 }
  rw [linearIndependent_equiv' e]
  · exact this
  · rfl

lemma Polynomial.finset_linearIndependent_of_degree_distinct
    (s : Finset ι)
    (ne_zero : ∀ i, i ∈ s → B i ≠ 0)
    (degree_distinct : ∀ (i j), i ∈ s → j ∈ s → i ≠ j → (B i).degree ≠ (B j).degree) :
    LinearIndependent R (fun i : s ↦ B i) := by
  refine finset_linearIndependent_of_natDegree_distinct _ _ _ ne_zero ?_
  intro i j hi hj hij
  specialize degree_distinct i j hi hj hij
  rw [degree_eq_natDegree (by aesop), degree_eq_natDegree (by aesop)] at degree_distinct
  exact_mod_cast degree_distinct


lemma Polynomial.linearIndependent_of_degree_distinct
    (ne_zero : ∀ i, B i ≠ 0)
    (degree_distinct : ∀ i j, i ≠ j → (B i).degree ≠ (B j).degree) :
    LinearIndependent R B := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  refine finset_linearIndependent_of_degree_distinct R B _  (by aesop) (by aesop)
