-- /-
-- Copyright (c) 2021 Jujian Zhang. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Jujian Zhang, Eric Wieser
-- -/

-- import Mathlib.Algebra.GradedMonoid
-- import Mathlib.Algebra.Group.Submonoid.Operations
-- import Mathlib.RingTheory.GradedAlgebra.Basic

-- /-!

-- # some instance on the zeroth grade of a graded object

-- -/

-- namespace SetLike


-- namespace GradeZero

-- variable {ι S R : Type*} [SetLike S R] [Monoid R] [AddMonoid ι]

-- variable {A : ι → S} [SetLike.GradedMonoid A]

-- variable (A) in

-- /-- The submonoid `A 0` of `R`. -/
-- @[simps]
-- def submonoid : Submonoid R where
--   carrier := A 0
--   mul_mem' ha hb := add_zero (0 : ι) ▸ SetLike.mul_mem_graded ha hb
--   one_mem' := SetLike.one_mem_graded A

-- /-- The monoid `A 0` inherited from `R` in the presence of `SetLike.GradedMonoid A`. -/
-- instance instMonoid : Monoid (A 0) := inferInstanceAs $ Monoid $ submonoid A

-- /-- The linter message "error: SetLike.GradeZero.coe_one.{u_3, u_2, u_1} Left-hand side does
--   not simplify, when using the simp lemma on itself." is wrong. The LHS does simplify. -/
-- @[nolint simpNF, simp, norm_cast] theorem coe_one : ↑(1 : A 0) = (1 : R) := rfl

-- /-- The linter message "error: SetLike.GradeZero.coe_mul.{u_3, u_2, u_1} Left-hand side does
--   not simplify, when using the simp lemma on itself." is wrong. The LHS does simplify. -/
-- @[nolint simpNF, simp, norm_cast] theorem coe_mul (a b : A 0) : ↑(a * b) = (↑a * ↑b : R) := rfl

-- /-- The linter message "error: SetLike.GradeZero.coe_pow.{u_3, u_2, u_1} Left-hand side does
--   not simplify, when using the simp lemma on itself." is wrong. The LHS does simplify. -/
-- @[nolint simpNF, simp, norm_cast] theorem coe_pow (a : A 0) (n : ℕ) : ↑(a ^ n) = (↑a : R) ^ n := rfl

-- end GradeZero

-- namespace GradeZero

-- variable {ι S R : Type*} [AddMonoid ι] [DecidableEq ι]
-- variable [Semiring R] [SetLike S R] [AddSubmonoidClass S R]

-- variable (A : ι → S) [GradedRing A]

-- @[simps]
-- def subsemiring : Subsemiring R where
--   carrier := A 0
--   mul_mem' := (submonoid A).mul_mem
--   one_mem' := (submonoid A).one_mem
--   add_mem' := add_mem
--   zero_mem' := zero_mem _

-- instance : Semiring (A 0) := inferInstanceAs $ Semiring $ subsemiring A

-- end GradeZero

-- namespace GradeZero

-- variable {ι S R : Type*} [AddMonoid ι] [DecidableEq ι]
-- variable [Ring R] [SetLike S R] [AddSubgroupClass S R]

-- variable (A : ι → S) [GradedRing A]

-- @[simps]
-- def subring : Subring R where
--   carrier := A 0
--   mul_mem' := (submonoid A).mul_mem
--   one_mem' := (submonoid A).one_mem
--   add_mem' := add_mem
--   zero_mem' := zero_mem _
--   neg_mem' := neg_mem

-- instance : Ring (A 0) := inferInstanceAs $ Ring $ subring A

-- end GradeZero

-- namespace GradeZero

-- variable {ι S R : Type*} [AddMonoid ι] [DecidableEq ι]
-- variable [CommSemiring R] [SetLike S R] [AddSubmonoidClass S R]

-- variable (A : ι → S) [GradedRing A]

-- instance : CommSemiring (A 0) where
-- __ := (inferInstance : Semiring (A 0))
-- mul_comm := by
--   rintro ⟨a, ha⟩ ⟨b, hb⟩
--   ext
--   simpa using mul_comm _ _

-- end GradeZero

-- namespace GradeZero

-- variable {ι S R : Type*} [AddMonoid ι] [DecidableEq ι]
-- variable [CommRing R] [SetLike S R] [AddSubgroupClass S R]

-- variable (A : ι → S) [GradedRing A]

-- instance : CommRing (A 0) where
-- __ := (inferInstance : Ring (A 0))
-- mul_comm := by
--   rintro ⟨a, ha⟩ ⟨b, hb⟩
--   ext
--   simpa using mul_comm _ _

-- end GradeZero

-- end SetLike
