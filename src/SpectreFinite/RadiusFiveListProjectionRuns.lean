module

public import SpectreFinite.RadiusFiveListProjectionIdentity
public import Init.Data.List.Nat.TakeDrop

@[expose] public section

namespace SpectreFinite.HexSearch.HigherFastChecking
universe u

theorem list_ofFn_getD_drop_take {α : Type u}
    (row : List α) (fallback : α) (start count : Nat)
    (hlen : count ≤ (row.drop start).length) :
    List.ofFn (fun i : Fin count => row[start + i.val]?.getD fallback) =
      (row.drop start).take count := by
  have hlength : ((row.drop start).take count).length = count :=
    List.length_take_of_le hlen
  have h := list_ofFn_getD_eq_self_of_length
    ((row.drop start).take count) fallback hlength
  have hfun :
      (fun i : Fin count => ((row.drop start).take count)[i.val]?.getD fallback) =
      (fun i : Fin count => row[start + i.val]?.getD fallback) := by
    funext i
    rw [List.getElem?_take_of_lt i.isLt, List.getElem?_drop]
  rw [hfun] at h
  exact h

#print axioms list_ofFn_getD_drop_take
end SpectreFinite.HexSearch.HigherFastChecking
