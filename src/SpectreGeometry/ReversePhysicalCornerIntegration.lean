module

public import SpectreGeometry.ReversePhysicalClusterPathsData
public import SpectreGeometry.ReversePhysicalClusterReal
public import SpectreGeometry.ReverseCornerCocycle

@[expose] public section


namespace SpectreGeometry.ReversePhysicalCluster
noncomputable section
open SpectreFinite SpectreFinite.HexSearch SpectreGeometry.ReverseExistence SpectreClusters.ReverseExistence

def physicalCornerReal (a : State) (d : Fin 6) : RealPoint :=
  quarterPoint (physicalStateCorner4 a d)

def physicalPathReal (a : State) (d : Fin 6) : List RealPoint :=
  (physicalStatePath4 a d).map quarterPoint

theorem physical_corner_matching (hcert : ∀ k, PhysicalBoundaryCertificate k) :
    CornerMatching physicalCornerReal := by
  rintro ⟨k,r⟩ ⟨j,s⟩ d h
  have he := congrArg quarterPoint ((hcert k r j s d h).1)
  simpa only [physicalDelta4,quarterPoint_sub,cornerDisplacement,physicalCornerReal] using he

theorem physical_real_path_reversal (hcert : ∀ k, PhysicalBoundaryCertificate k)
    (a b : State) (d : Fin 6) (h : sideMatch a b d) :
    physicalPathReal a d = ((physicalPathReal b (opposite d)).reverse).map
      (fun p => cornerDisplacement physicalCornerReal a b d + p) := by
  obtain ⟨k,r⟩ := a
  obtain ⟨j,s⟩ := b
  unfold physicalPathReal
  rw [(hcert k r j s d h).2]
  simp only [List.map_map,List.map_reverse,Function.comp_def,
    quarterPoint_add,physicalDelta4,quarterPoint_sub,cornerDisplacement,physicalCornerReal]

theorem physical_placed_path_gluing (hcert : ∀ k, PhysicalBoundaryCertificate k)
    (f : Position → State) (hf : GloballyLegal f) (A : Position → RealPoint)
    (hA : ∀ x d, A (addPos x (SpectreFinite.direction d)) = A x +
      cornerDisplacement physicalCornerReal (f x) (f (addPos x (SpectreFinite.direction d))) d)
    (x : Position) (d : Fin 6) :
    (physicalPathReal (f x) d).map (fun p => A x+p) =
      ((physicalPathReal (f (addPos x (SpectreFinite.direction d))) (opposite d)).map
        (fun p => A (addPos x (SpectreFinite.direction d))+p)).reverse := by
  rw [physical_real_path_reversal hcert _ _ d (field_sideMatch f hf x d)]
  simp only [List.map_map,List.map_reverse,Function.comp_def,hA x d,add_assoc]

/-- The checked finite physical boundary rules integrate to real translations
on the entire legal marked field, with complete reversed path agreement.
Coverage, injectivity, and disjointness are separate obligations. -/
theorem exists_physical_translation_field (hcert : ∀ k, PhysicalBoundaryCertificate k)
    (f : Position → State) (hf : GloballyLegal f) :
    ∃ A : Position → RealPoint, A (0,0)=0 ∧
      (∀ x d, A (addPos x (SpectreFinite.direction d)) = A x +
        cornerDisplacement physicalCornerReal (f x) (f (addPos x (SpectreFinite.direction d))) d) ∧
      ∀ x d, (physicalPathReal (f x) d).map (fun p => A x+p) =
        ((physicalPathReal (f (addPos x (SpectreFinite.direction d))) (opposite d)).map
          (fun p => A (addPos x (SpectreFinite.direction d))+p)).reverse := by
  obtain ⟨A,h0,hA⟩ := exists_cornerAnchor physicalCornerReal
    (physical_corner_matching hcert) f hf
  exact ⟨A,h0,hA,physical_placed_path_gluing hcert f hf A hA⟩

end
end SpectreGeometry.ReversePhysicalCluster
