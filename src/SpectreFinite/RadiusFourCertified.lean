module

public import SpectreFinite.RadiusFourFamilyData
public import SpectreFinite.HexRegionGeometry
public import SpectreFinite.RadiusFourRoot0
public import SpectreFinite.RadiusFourRoot1
public import SpectreFinite.RadiusFourRoot2
public import SpectreFinite.RadiusFourRoot3
public import SpectreFinite.RadiusFourRoot4
public import SpectreFinite.RadiusFourRoot5
public import SpectreFinite.RadiusFourRoot6
public import SpectreFinite.RadiusFourRoot7
public import SpectreFinite.RadiusFourRoot8

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem extract_mem_familyForKind (f : Position → State) (hf : GloballyLegal f)
    (center : Position) : ∀ k : TileKind, f center = (k,0) →
    extract f center (hexRegion 4) ∈ familyForKind k := by
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
    (hf : GloballyLegal f) : OccurrenceComplete f (hexRegion 4) allTurnFamily := by
  apply rotationClosure_occurrenceComplete (hexRegion 4) (hexRegion_rotation 4) familyForKind ?_ f hf
  intro k g hg hroot
  simpa only [extract_zero_eq_restriction] using extract_mem_familyForKind g hg (0,0) k hroot
theorem extract_mem_allTurnFamily (f : Position → State) (hf : GloballyLegal f)
    (center : Position) : extract f center (hexRegion 4) ∈ allTurnFamily :=
  allTurnFamily_occurrenceComplete f hf center
#print axioms allTurnFamily_occurrenceComplete
#print axioms extract_mem_allTurnFamily
end SpectreFinite.HexSearch.RadiusFour
