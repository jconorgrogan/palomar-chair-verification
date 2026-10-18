module

public import SpectreFinite.RadiusFiveFamilyData
public import SpectreFinite.HexRegionGeometry
public import SpectreFinite.RadiusFiveRoot0
public import SpectreFinite.RadiusFiveRoot1
public import SpectreFinite.RadiusFiveRoot2
public import SpectreFinite.RadiusFiveRoot3
public import SpectreFinite.RadiusFiveRoot4
public import SpectreFinite.RadiusFiveRoot5
public import SpectreFinite.RadiusFiveRoot6
public import SpectreFinite.RadiusFiveRoot7
public import SpectreFinite.RadiusFiveRoot8

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem extract_mem_familyForKind (f : Position → State) (hf : GloballyLegal f)
    (center : Position) : ∀ k : TileKind, f center = (k,0) →
    extract f center (hexRegion 5) ∈ familyForKind k := by
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
    (hf : GloballyLegal f) : OccurrenceComplete f (hexRegion 5) allTurnFamily := by
  apply rotationClosure_occurrenceComplete (hexRegion 5) (hexRegion_rotation 5) familyForKind ?_ f hf
  intro k g hg hroot
  simpa only [extract_zero_eq_restriction] using extract_mem_familyForKind g hg (0,0) k hroot
theorem extract_mem_allTurnFamily (f : Position → State) (hf : GloballyLegal f)
    (center : Position) : extract f center (hexRegion 5) ∈ allTurnFamily :=
  allTurnFamily_occurrenceComplete f hf center
#print axioms allTurnFamily_occurrenceComplete
#print axioms extract_mem_allTurnFamily
end SpectreFinite.HexSearch.RadiusFive
