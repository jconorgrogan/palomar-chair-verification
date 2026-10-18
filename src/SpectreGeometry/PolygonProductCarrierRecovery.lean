module

public import SpectreGeometry.PolygonProductGlobalFlattening
public import SpectreGeometry.SingleTileReplacementUniqueness

@[expose] public section


namespace SpectreGeometry
noncomputable section
open Set

theorem polygon_product_closure_interior :
    closure (interior polygonProductBody) = polygonProductBody := by
  have hi : productCoordinates '' interior (polygonBody ×ˢ polygonBody) =
      interior polygonProductBody := productCoordinates.toHomeomorph.image_interior _
  calc
    closure (interior polygonProductBody) =
        closure (productCoordinates '' interior (polygonBody ×ˢ polygonBody)) := congrArg closure hi.symm
    _ = productCoordinates '' closure (interior (polygonBody ×ˢ polygonBody)) :=
      (productCoordinates.toHomeomorph.image_closure _).symm
    _ = polygonProductBody := by
      rw [interior_prod_eq,closure_prod_eq,polygonBody_closure_interior]
      rfl

theorem placed_product_closure_interior (f : EFour ≃ᵢ EFour) :
    closure (interior (f '' polygonProductBody)) = f '' polygonProductBody := by
  have hi : f '' interior polygonProductBody = interior (f '' polygonProductBody) :=
    f.toHomeomorph.image_interior _
  calc
    closure (interior (f '' polygonProductBody)) = closure (f '' interior polygonProductBody) :=
      congrArg closure hi.symm
    _ = f '' closure (interior polygonProductBody) := (f.toHomeomorph.image_closure _).symm
    _ = f '' polygonProductBody := by rw [polygon_product_closure_interior]

/-- Any alternative pose for the same physical tile in a physical tiling
has exactly the same raw carrier. This needs no assertion that the keyed
body has a trivial internal symmetry group. -/
theorem physical_equal_keyed_carrier_equal_raw {I : Type*}
    (f : I → EFour ≃ᵢ EFour) (T : PolygonProductPhysicalTiling f)
    (root : I) (g : EFour ≃ᵢ EFour)
    (hbody : g '' polygonProductKeyBody = f root '' polygonProductKeyBody) :
    g '' polygonProductBody = f root '' polygonProductBody := by
  classical
  let F : I → EFour ≃ᵢ EFour := fun i => if i = root then g else f i
  have hF (i : I) : F i '' polygonProductKeyBody = f i '' polygonProductKeyBody := by
    by_cases hi : i = root
    · subst i; simpa [F] using hbody
    · simp [F,hi]
  have TF : PolygonProductPhysicalTiling F := by
    constructor
    · intro i j hij
      change Disjoint (interior (F i '' polygonProductKeyBody))
        (interior (F j '' polygonProductKeyBody))
      rw [hF,hF]
      exact T.interiors_disjoint hij
    · intro x
      obtain ⟨i,hi⟩ := T.covers x
      refine ⟨i,?_⟩
      change x ∈ F i '' polygonProductKeyBody
      rw [hF]
      exact hi
  obtain ⟨hfc,hfp⟩ := physical_raw_product_tiling T
  obtain ⟨hFc,hFp⟩ := physical_raw_product_tiling TF
  have hreg (p : EFour ≃ᵢ EFour) :
      p '' polygonProductBody ⊆ closure (interior (p '' polygonProductBody)) := by
    rw [placed_product_closure_interior]
  have he := single_tile_replacement_unique
    (fun i => f i '' polygonProductBody) (fun i => F i '' polygonProductBody) root
    (fun i => hreg (f i)) (fun i => hreg (F i))
    (polygon_product_body_isCompact.image (f root).continuous).isClosed
    (polygon_product_body_isCompact.image (F root).continuous).isClosed
    hfp hFp hfc hFc (by intro i hi; simp [F,hi])
  simpa [F] using he.symm

end
end SpectreGeometry
