module

public import SpectreFinite.WindowRotationClosure
public import SpectreFinite.RadiusTwoTheta
public import SpectreFinite.RadiusTwoRoot0
public import SpectreFinite.RadiusTwoRoot1
public import SpectreFinite.RadiusTwoRoot3
public import SpectreFinite.RadiusTwoRoot4
public import SpectreFinite.RadiusTwoRoot5
public import SpectreFinite.RadiusTwoRoot6
public import SpectreFinite.RadiusTwoRoot7
public import SpectreFinite.RadiusTwoRoot8

@[expose] public section


/-! Certified radius-two occurrence family for all root kinds and turns.
The finite table certificates imply coverage only: no existence, exact global
extendibility, parent recognition, or physical correspondence is asserted. -/
namespace SpectreFinite.HexSearch.RadiusTwo
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def familyForKind (k : TileKind) : List Patch :=
  match k.val with
  | 0 => root0Family
  | 1 => root1Family
  | 2 => thetaFamily
  | 3 => root3Family
  | 4 => root4Family
  | 5 => root5Family
  | 6 => root6Family
  | 7 => root7Family
  | _ => root8Family

theorem extract_mem_familyForKind (f : Position → State) (hf : GloballyLegal f)
    (center : Position) : ∀ k : TileKind, f center = (k,0) →
    extract f center (hexRegion 2) ∈ familyForKind k := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (fun i => Fin.elim0 i)))))))))
  · exact extract_mem_root0Family f hf center
  · exact extract_mem_root1Family f hf center
  · exact extract_mem_thetaFamily f hf center
  · exact extract_mem_root3Family f hf center
  · exact extract_mem_root4Family f hf center
  · exact extract_mem_root5Family f hf center
  · exact extract_mem_root6Family f hf center
  · exact extract_mem_root7Family f hf center
  · exact extract_mem_root8Family f hf center

def turnZeroFamily : List Patch := (List.finRange 9).flatMap familyForKind

theorem familyForKind_counts : (List.finRange 9).map (fun k => (familyForKind k).length) =
    [22,21,1,4,18,17,18,30,22] := by decide

theorem turnZeroFamily_count : turnZeroFamily.length = 153 := by decide

def allTurnFamily : List Patch := rotationClosure (hexRegion 2) familyForKind

theorem allTurnFamily_count : allTurnFamily.length = 918 := by decide

theorem allTurnFamily_occurrenceComplete (f : Position → State)
    (hf : GloballyLegal f) : OccurrenceComplete f (hexRegion 2) allTurnFamily := by
  apply rotationClosure_occurrenceComplete (hexRegion 2) hexRegion_two_rotation familyForKind ?_ f hf
  intro k g hg hroot
  simpa only [extract_zero_eq_restriction] using extract_mem_familyForKind g hg (0,0) k hroot

theorem extract_mem_allTurnFamily (f : Position → State) (hf : GloballyLegal f)
    (center : Position) : extract f center (hexRegion 2) ∈ allTurnFamily :=
  allTurnFamily_occurrenceComplete f hf center

#print axioms extract_mem_familyForKind
#print axioms allTurnFamily_occurrenceComplete
#print axioms extract_mem_allTurnFamily
end SpectreFinite.HexSearch.RadiusTwo
