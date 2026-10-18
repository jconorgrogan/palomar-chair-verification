module

public import SpectreFinite.RadiusThreeFamilyData
public import SpectreFinite.HexRegionGeometry
public import SpectreFinite.RadiusThreeRoot0
public import SpectreFinite.RadiusThreeRoot1
public import SpectreFinite.RadiusThreeRoot2
public import SpectreFinite.RadiusThreeRoot3
public import SpectreFinite.RadiusThreeRoot4
public import SpectreFinite.RadiusThreeRoot5
public import SpectreFinite.RadiusThreeRoot6
public import SpectreFinite.RadiusThreeRoot7
public import SpectreFinite.RadiusThreeRoot8

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem extract_mem_familyForKind (f : Position → State) (hf : GloballyLegal f)
    (center : Position) : ∀ k : TileKind, f center = (k,0) →
    extract f center (hexRegion 3) ∈ familyForKind k := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (fun i => Fin.elim0 i)))))))))
  · exact extract_mem_root0Family f hf center
  · exact extract_mem_root1Family f hf center
  · exact extract_mem_root2Family f hf center
  · exact extract_mem_root3Family f hf center
  · exact extract_mem_root4Family f hf center
  · exact extract_mem_root5Family f hf center
  · exact extract_mem_root6Family f hf center
  · exact extract_mem_root7Family f hf center
  · exact extract_mem_root8Family f hf center
theorem allTurnFamily_occurrenceComplete (f : Position → State)
    (hf : GloballyLegal f) : OccurrenceComplete f (hexRegion 3) allTurnFamily := by
  apply rotationClosure_occurrenceComplete (hexRegion 3) (hexRegion_rotation 3) familyForKind ?_ f hf
  intro k g hg hroot
  simpa only [extract_zero_eq_restriction] using extract_mem_familyForKind g hg (0,0) k hroot
theorem extract_mem_allTurnFamily (f : Position → State) (hf : GloballyLegal f)
    (center : Position) : extract f center (hexRegion 3) ∈ allTurnFamily :=
  allTurnFamily_occurrenceComplete f hf center
#print axioms allTurnFamily_occurrenceComplete
#print axioms extract_mem_allTurnFamily
end SpectreFinite.HexSearch.RadiusThree
