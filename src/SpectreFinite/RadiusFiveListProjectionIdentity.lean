module

public import Init.Data.List.OfFn

@[expose] public section


namespace SpectreFinite.HexSearch.HigherFastChecking
universe u

theorem list_ofFn_getD_eq_self {α : Type u} (row : List α) (fallback : α) :
    List.ofFn (fun i : Fin row.length => row[i.val]?.getD fallback) = row := by
  have h : (fun i : Fin row.length => row[i.val]?.getD fallback) =
      (fun i : Fin row.length => row[i.val]) := by
    funext i
    simp only [List.getElem?_eq_getElem i.isLt, Option.getD_some]
  rw [h]
  exact List.ofFn_getElem

theorem list_ofFn_getD_eq_self_of_length {α : Type u} {n : Nat}
    (row : List α) (fallback : α) (hlen : row.length = n) :
    List.ofFn (fun i : Fin n => row[i.val]?.getD fallback) = row := by
  subst n
  exact list_ofFn_getD_eq_self row fallback

#print axioms list_ofFn_getD_eq_self
#print axioms list_ofFn_getD_eq_self_of_length
end SpectreFinite.HexSearch.HigherFastChecking
