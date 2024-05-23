import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent

open Polynomial

variable (R : Type*) [Ring R]
variable {ι : Type*} (B : ι → R[X])

lemma Polynomial.finset_linearIndependent_of_natDegree_distinct
    (s : Finset ι)
    (ne_zero : ∀ i, i ∈ s → B i ≠ 0)
    (degree_distinct : ∀ (i j), i ∈ s → j ∈ s → i ≠ j → (B i).natDegree ≠ (B j).natDegree) :
    LinearIndependent R (fun i : s ↦ B i) := by
  -- suffices ∀ (n : ℕ) (s : Finset ι) (hs : ∀ i, i ∈ s → (B i).natDegree ≤ n) (ne_zero : ∀ i, i ∈ s → B i ≠ 0)
  --     (degree_distinct : ∀ (i j), i ∈ s → j ∈ s → i ≠ j → (B i).natDegree ≠ (B j).natDegree),
  --     LinearIndependent R (fun i : s ↦ B i) from
  --   this (s.sup fun i ↦ (B i).natDegree) s
  --     (by intro i hi; exact s.le_sup (f := fun i ↦ (B i).natDegree) hi)
  --     ne_zero degree_distinct

  -- refine Nat.rec ?_ ?_
  -- · simp only [Nat.zero_eq, nonpos_iff_eq_zero, ne_eq]
  --   intro s hs ne_zero degree_distinct
  --   simp_rw [natDegree_eq_zero] at hs
  --   choose x hx using hs
  --   by_cases card : s.card ≤ 1
  --   · rw [Finset.card_le_one] at card
  --     by_cases ne : s = ∅
  --     · subst ne
  --       exact linearIndependent_empty_type

  --     let instU : Unique s :=
  --     ⟨⟨⟨Finset.nonempty_of_ne_empty ne |>.choose, Finset.nonempty_of_ne_empty ne |>.choose_spec⟩⟩,
  --       by rintro ⟨x, hx⟩; ext; apply card _ hx _ (Finset.nonempty_of_ne_empty ne |>.choose_spec)⟩
  --     exact linearIndependent_unique (fun i : s ↦ B i) <| ne_zero _ <|
  --       Finset.nonempty_of_ne_empty ne |>.choose_spec
  --   replace card : 1 < s.card := by omega
  --   rw [Finset.one_lt_card] at card
  --   obtain ⟨i, hi, j, hj, hij⟩ := card

  --   exfalso
  --   refine degree_distinct i j hi hj hij ?_
  --   rw [← hx i hi, ← hx j hj]
  --   simp

  -- -- induction step
  -- intro n IH s max_degree ne_zero degree_distinct
  -- rw [linearIndependent_iff']

  sorry

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
  refine finset_linearIndependent_of_degree_distinct R B _ (by aesop) (by aesop)
