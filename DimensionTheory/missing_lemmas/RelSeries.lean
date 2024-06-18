import Mathlib.Order.RelSeries
import Mathlib.Order.Cover

namespace LTSeries

variable {α : Type*} [Preorder α]

lemma longestOf_covBy [FiniteDimensionalOrder α]
    (i : Fin (LTSeries.longestOf α).length) :
    LTSeries.longestOf α i.castSucc ⋖ LTSeries.longestOf α i.succ := by
  refine ⟨(LTSeries.longestOf α).step i, ?_⟩
  by_contra! rid
  obtain ⟨a, ha1, ha2⟩ := rid
  simpa [RelSeries.insertNth_length, add_le_iff_nonpos_right, nonpos_iff_eq_zero] using
    LTSeries.longestOf_is_longest <| (LTSeries.longestOf α).insertNth i a ha1 ha2

end LTSeries
