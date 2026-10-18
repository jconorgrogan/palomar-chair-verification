module

public import SpectreGeometry.PolygonProductForwardPairing
public import LiteralPlanar.OrientedSourceEdges

@[expose] public section


namespace SpectreGeometry
noncomputable section
open Set

/-- The literal keyed product construction works for any two proper planar
P tilings. All matching premises are discharged by physical edge registration. -/
theorem physical_product_tiling_of_planar_tilings {I J : Type*}
    (f : I → EPlane ≃ᵢ EPlane) (g : J → EPlane ≃ᵢ EPlane)
    (hf : ∀ i, DirectPlacement (f i)) (hg : ∀ j, DirectPlacement (g j))
    (hfc : ∀ x, ∃ i, x ∈ f i '' euclideanBody)
    (hgc : ∀ x, ∃ j, x ∈ g j '' euclideanBody)
    (hfp : Pairwise fun i j => Disjoint (interior (f i '' euclideanBody))
      (interior (f j '' euclideanBody)))
    (hgp : Pairwise fun i j => Disjoint (interior (g i '' euclideanBody))
      (interior (g j '' euclideanBody))) :
    PolygonProductPhysicalTiling (fun ij : I × J => productPlacement (f ij.1) (g ij.2)) := by
  apply physical_product_tiling_of_planar_partners f g hf hg hfc hgc hfp hgp
  · exact LiteralPlanar.Forward.homochiral_source_edges_have_reversed_partner f hf hfc hfp
  · exact LiteralPlanar.Forward.homochiral_source_edges_have_reversed_partner g hg hgc hgp

/-- Exact seed interface for the already-proved whole-plane P existence
statement. The seed premise is retained visibly until its checked application. -/
theorem exists_physical_product_tiling_of_planar_seed
    (seed : ∃ (I : Type) (p : I → EPlane ≃ᵢ EPlane),
      (∀ i, DirectPlacement (p i)) ∧
      (∀ x : EPlane, ∃ i, x ∈ p i '' euclideanBody) ∧
      Pairwise (fun i j => Disjoint (interior (p i '' euclideanBody))
        (interior (p j '' euclideanBody))) ∧
      LocallyFinite (fun i => p i '' euclideanBody)) :
    ∃ (I : Type) (f : I → EFour ≃ᵢ EFour), PolygonProductPhysicalTiling f := by
  obtain ⟨I,p,hd,hc,hp,_⟩ := seed
  exact ⟨I × I,fun ij => productPlacement (p ij.1) (p ij.2),
    physical_product_tiling_of_planar_tilings p p hd hd hc hc hp hp⟩

end
end SpectreGeometry
