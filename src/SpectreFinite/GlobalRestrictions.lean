module

public import SpectreFinite.HexSearchModel

@[expose] public section


/-! Every globally matching marked-hexagon grid restricts to the complete
finite search. This is a discrete implication; it does not assume or prove
existence of such a grid or its physical Tile(1,1) correspondence. -/
namespace SpectreFinite.HexSearch

def GloballyLegal (f : Position → State) : Prop :=
  ∀ x y : Position, x ≠ y → Matches (x,f x) (y,f y)

def restriction (f : Position → State) (positions : List Position) :
    List (Position × State) := positions.map (fun x => (x,f x))

theorem restriction_pairwise (f : Position → State) (hf : GloballyLegal f)
    (positions : List Position) (hn : positions.Nodup) :
    (restriction f positions).Pairwise Matches := by
  induction positions with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    have hns := List.nodup_cons.mp hn
    apply List.Pairwise.cons
    · intro y hy
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hy
      exact hf x z (fun he => hns.1 (he ▸ hz))
    · exact ih hns.2

/-- A genuine global matching field cannot be omitted by the exact finite
branching algorithm on any specified distinct list of positions. -/
theorem restriction_enumerated (f : Position → State) (hf : GloballyLegal f)
    (positions : List Position) (hn : positions.Nodup) :
    restriction f positions ∈ assignments positions := by
  apply (mem_assignments_iff positions _).mpr
  exact ⟨by simp [restriction,List.map_map,Function.comp_def], restriction_pairwise f hf positions hn⟩

/-- The actual fixed 91-position domain inherits the complete-search bound.
No enumeration of its possible assignments is claimed to have run. -/
theorem radiusFive_restriction_enumerated (f : Position → State) (hf : GloballyLegal f) :
    restriction f (hexRegion 5) ∈ assignments (hexRegion 5) :=
  restriction_enumerated f hf (hexRegion 5) hexRegion_five_nodup

#print axioms restriction_pairwise
#print axioms restriction_enumerated
#print axioms radiusFive_restriction_enumerated
end SpectreFinite.HexSearch
