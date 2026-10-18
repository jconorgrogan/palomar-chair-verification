module

public import SpectreFinite.WindowTableCoverage

@[expose] public section


/-! Generic coordinate lookup on a zipped row. This lets a projected table
prove its coordinate calculation once, without redoing it for every row. -/
namespace SpectreFinite.HexSearch

theorem patchState_zip_index (domain : List Position) (row : List State)
    (p : Position) (index : Nat)
    (hindex : domain[index]? = some p)
    (hfirst : ∀ j : Fin index, domain[j.val]? ≠ some p) :
    patchState (domain.zip row) p = (row[index]?).getD (0,0) := by
  induction domain generalizing row index with
  | nil => simp at hindex
  | cons a rest ih =>
    cases index with
    | zero =>
      have ha : a = p := by simpa using hindex
      subst p
      cases row with
      | nil => rfl
      | cons s ss => simp [patchState]
    | succ index =>
      have ha : a ≠ p := by
        have h := hfirst ⟨0, Nat.zero_lt_succ index⟩
        simpa using h
      have hi : rest[index]? = some p := by simpa using hindex
      have hf : ∀ j : Fin index, rest[j.val]? ≠ some p := by
        intro j
        have h := hfirst ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩
        simpa using h
      cases row with
      | nil => simp [patchState]
      | cons s ss => simpa [patchState, ha] using ih ss index hi hf

#print axioms patchState_zip_index
end SpectreFinite.HexSearch
