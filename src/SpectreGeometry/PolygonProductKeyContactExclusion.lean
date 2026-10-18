module

public import SpectreGeometry.PolygonProductKeyBody
public import PhysicalRegistration.IsometryTransport

@[expose] public section


/-! Actual local contact exclusion for arbitrary Euclidean placements of the
literal optimized P×P keyed body. The three graph-window membership premises
and pairwise interior disjointness are explicit; no companion or recognition
hypothesis is hidden in the conclusion. -/
namespace SpectreGeometry
noncomputable section
open Set PhysicalRegistration

def placedPolygonProductKeyBody (f : EFour ≃ᵢ EFour) : Set EFour :=
  f '' polygonProductKeyBody

def placedProductKeyGraphWindow (f : EFour ≃ᵢ EFour) (s : ProductKeySite) : Set EFour :=
  f '' productKeyGraphWindow s

def placedProductKeyGraphWindow_local_graph (f : EFour ≃ᵢ EFour) (s : ProductKeySite)
    (y : EFour) (hy : y ∈ placedProductKeyGraphWindow f s) :
    LocalLipschitzGraphAt (placedPolygonProductKeyBody f) y (34/4357) := by
  let hexists : ∃ x, x ∈ productKeyGraphWindow s ∧ f x = y := hy
  let x := Classical.choose hexists
  have hx : x ∈ productKeyGraphWindow s := (Classical.choose_spec hexists).1
  have hxy : f x = y := (Classical.choose_spec hexists).2
  rw [← hxy]
  exact (polygonProductKeyBody_graph_window_local_graph s x hx).mapIsometry f

/-- No three actual key-graph windows on interior-disjoint placed bodies meet.
This includes their lower-dimensional junctions and uses arbitrary isometries. -/
theorem no_three_placed_polygon_product_key_graph_windows
    (f : Fin 3 → EFour ≃ᵢ EFour) (s : Fin 3 → ProductKeySite) (y : EFour)
    (hy : ∀ i, y ∈ placedProductKeyGraphWindow (f i) (s i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedPolygonProductKeyBody (f i)))
        (interior (placedPolygonProductKeyBody (f j)))) : False :=
  no_three_local_graphs (fun i => placedPolygonProductKeyBody (f i)) y (34/4357)
    product_key_slope_below_half.1 product_key_slope_below_half.2
    (fun i => placedProductKeyGraphWindow_local_graph (f i) (s i) y (hy i)) hdisjoint

end
end SpectreGeometry
