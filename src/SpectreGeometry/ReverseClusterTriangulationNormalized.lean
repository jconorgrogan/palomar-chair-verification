module

public import SpectreGeometry.ReverseClusterTriangulationCarriers
public import SpectreGeometry.ReverseClusterTriangulationHexBinding

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
noncomputable section
open Set SpectreClusters

/-- Exact binding of all nine finite source halfplane packets to the fixed hex. -/
theorem all_source_hex_facets_bound : ∀ k : Fin 9,
    sourceHexFacets k = baseHexFacets.map (dilateFacet (sourceScale k)) := by decide

/-- The actual finite source mesh carrier, after its declared normalization. -/
theorem all_normalized_source_carriers_exact (k : Fin 9) :
    (fun x : RealPoint => (1/(3*(sourceScale k : ℝ))) • x) ''
      familyBody (sourceFamily k) = standardHexBody := by
  rw [all_source_carriers_exact,all_source_hex_facets_bound]
  simpa only [Int.cast_natCast] using normalize_dilated_hex (sourceScale k)
    (by exact_mod_cast all_source_scales_positive k)

/-- The finite source mesh uses exactly the source cells of the all-plane cover. -/
theorem all_normalized_source_carriers_eq_sourceHexCarrier (k : Fin 9) :
    (fun x : RealPoint => (1/(3*(sourceScale k : ℝ))) • x) ''
      familyBody (sourceFamily k) =
        SpectreGeometry.ReverseExistence.sourceHexCarrier (0,0) := by
  rw [all_normalized_source_carriers_exact,standardHexBody_eq_sourceHexCarrier_zero]

/-- The same source normalization at every integer center. -/
theorem all_translated_source_carriers_exact (k : Fin 9) (c : ℤ × ℤ) :
    (fun x : RealPoint => (1/(3*(sourceScale k : ℝ))) • x + integerPoint c) ''
      familyBody (sourceFamily k) =
        SpectreGeometry.ReverseExistence.sourceHexCarrier c := by
  calc
    _ = (fun y : RealPoint => y + integerPoint c) ''
        ((fun x : RealPoint => (1/(3*(sourceScale k : ℝ))) • x) ''
          familyBody (sourceFamily k)) := by rw [Set.image_image]
    _ = (fun y : RealPoint => y + integerPoint c) '' standardHexBody := by
      rw [all_normalized_source_carriers_exact]
    _ = SpectreGeometry.ReverseExistence.sourceHexCarrier c :=
      translated_standardHexBody_eq_sourceHexCarrier c

end
end SpectreGeometry.ReverseClusterTriangulation
