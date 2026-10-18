module

public import SpectreFinite.FiniteTableCover

@[expose] public section


/-! Exact composition of exhaustive row checks. Every original row belongs
to an explicitly listed chunk; no row is filtered or assumed redundant. -/
namespace SpectreFinite.FiniteTable
universe u
variable {n : Nat} {State : Type u} [DecidableEq State]

theorem checkNarrowing_flatten (scope : List (Fin n))
    (chunks : List (List (List State))) (current proposed : Domains n State)
    (hcheck : chunks.all (fun rows =>
      checkNarrowing ⟨scope, rows⟩ current proposed) = true) :
    checkNarrowing ⟨scope, chunks.flatten⟩ current proposed = true := by
  apply List.all_eq_true.mpr
  intro row hrow
  obtain ⟨chunk, hchunk, hrow⟩ := List.mem_flatten.mp hrow
  exact List.all_eq_true.mp (List.all_eq_true.mp hcheck chunk hchunk) row hrow

#print axioms checkNarrowing_flatten
end SpectreFinite.FiniteTable
