module

public import SpectreFinite.WindowTableConstraints
public import SpectreFinite.FiniteTableCover

@[expose] public section


/-! Actual field windows reconstructed from certified finite-CSP output rows. -/
namespace SpectreFinite.HexSearch

def rowsToPatches {n : Nat} (positions : Fin n → Position)
    (rows : List (List State)) : List Patch :=
  rows.map (fun row => ((List.finRange n).map positions).zip row)

theorem fieldAssignment_reconstruct {n : Nat} (positions : Fin n → Position)
    (f : Position → State) (center : Position) :
    ((List.finRange n).map positions).zip
      (FiniteTable.fullProjection (fieldAssignment positions f center)) =
    extract f center ((List.finRange n).map positions) := by
  rw [FiniteTable.fullProjection, List.zip_map']
  simp [extract, restriction, shiftedField, fieldAssignment, List.map_map, Function.comp_def]

/-- This is one-way coverage, exactly sufficient for the global-window
invariant; no assertion that all output rows extend to a field is needed. -/
theorem extract_mem_of_table_cover {n : Nat} (positions : Fin n → Position)
    (base : List Position) (family : List Patch) (root : State)
    (centers : List Position) (outputs : List (List State))
    (hcover : FiniteTable.Covers (rootDomains positions root)
      (windowConstraints positions base family centers) outputs)
    (f : Position → State) (hfamily : OccurrenceComplete f base family)
    (center : Position) (hroot : f center = root) :
    extract f center ((List.finRange n).map positions) ∈ rowsToPatches positions outputs := by
  have hsol := fieldAssignment_solution positions base family f hfamily center centers
  rw [hroot] at hsol
  exact List.mem_map.mpr ⟨FiniteTable.fullProjection (fieldAssignment positions f center),
    hcover _ hsol, fieldAssignment_reconstruct positions f center⟩

/-- Direct trusted-kernel consumer of a true executable cover check. -/
theorem extract_mem_of_checked_cover {n : Nat} (positions : Fin n → Position)
    (base : List Position) (family : List Patch) (root : State)
    (centers : List Position) (outputs : List (List State))
    (depth : Nat) (certificate : FiniteTable.CoverCertificate n State)
    (hcheck : FiniteTable.checkCover depth (windowConstraints positions base family centers)
      outputs (rootDomains positions root) certificate = true)
    (f : Position → State) (hfamily : OccurrenceComplete f base family)
    (center : Position) (hroot : f center = root) :
    extract f center ((List.finRange n).map positions) ∈ rowsToPatches positions outputs :=
  extract_mem_of_table_cover positions base family root centers outputs
    (FiniteTable.checkCover_sound _ _ _ _ _ hcheck) f hfamily center hroot

end SpectreFinite.HexSearch
