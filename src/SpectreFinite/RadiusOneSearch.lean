module

public import SpectreFinite.GlobalRestrictions

@[expose] public section


/-! Raw seven-cell radius-one compatibility search with a fixed root state.
No quotient by rotations, reduced-patch classification, parent recognition,
physical correspondence, or aperiodicity statement is made. -/
namespace SpectreFinite.HexSearch.RadiusOne

def positions : List Position :=
  [(-1,1),(0,1),(1,0),(1,-1),(0,-1),(-1,0),(0,0)]

def choices (root : State) (p : Position) : List State :=
  if p = (0,0) then [root] else stateChoices

def assignments (root : State) : List (List (Position × State)) :=
  Search.enumerate (choices root) Matches positions

theorem positions_nodup : positions.Nodup := by decide

theorem positions_length : positions.length = 7 := rfl

theorem positions_mem_iff (p : Position) :
    p ∈ positions ↔ p ∈ hexRegion 1 := by
  have hp : positions.Perm (hexRegion 1) := by decide
  exact hp.mem_iff

theorem mem_choices_iff (root s : State) (p : Position) :
    s ∈ choices root p ↔ (p = (0,0) → s = root) := by
  by_cases h : p = (0,0)
  · simp [choices,h]
  · simp [choices,h,mem_stateChoices]

/-- Exact soundness and completeness for all 54 states at each nonroot cell,
with the root fixed. Pairwise matching is the frozen actual mark relation. -/
theorem mem_assignments_iff (root : State) (p : List (Position × State)) :
    p ∈ assignments root ↔ p.map Prod.fst = positions ∧ p.Pairwise Matches ∧
      ∀ x ∈ p, x.1 = (0,0) → x.2 = root := by
  rw [assignments,Search.mem_enumerate_iff]
  simp only [mem_choices_iff]

#print axioms positions_nodup
#print axioms positions_mem_iff
#print axioms mem_assignments_iff
end SpectreFinite.HexSearch.RadiusOne
