module

public import SpectreFinite.ParentOwnershipFiniteEncoding

@[expose] public section


/-! Extensional bridge to ordinary ordered position/state zip tables. -/
namespace SpectreFinite.HexSearch.ParentOwnership

theorem encodedPatch_eq_zip (row : List State) (hlen : row.length = 91) :
    encodedPatch row = (hexRegion 5).zip row := by
  apply List.ext_getElem
  · simp [encodedPatch, restriction, List.length_zip, hexRegion_five_size, hlen]
  · intro i hi hj
    have hi' : i < 91 := by
      simpa [encodedPatch, restriction, hexRegion_five_size] using hi
    have hp : i < (hexRegion 5).length := by simpa [hexRegion_five_size] using hi'
    have hr : i < row.length := by simpa [hlen] using hi'
    have hs := indexedField_at_index row ⟨i,hi'⟩
    simpa [encodedPatch, restriction, List.getElem_zip, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hr] using hs

#print axioms encodedPatch_eq_zip
end SpectreFinite.HexSearch.ParentOwnership
