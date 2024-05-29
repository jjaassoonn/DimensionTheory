import Init.Data.Int.Basic

theorem Int.coe_toNat_of_nonneg (z : Int) (hz : 0 ≤ z) : (z.toNat : Int) = z := by
  induction z with
  | ofNat z => rfl
  | negSucc z => simp at hz

@[norm_cast, simp]
theorem Int.coe_toNat_of_neg (z : Int) (hz : z < 0) : (z.toNat : Int) = 0 := by
  induction z with
  | ofNat z =>
    simp only [ofNat_eq_coe] at hz
    norm_cast at hz
  | negSucc z => rfl
