module

public import SpectreGeometry.PolygonProductIsometries

@[expose] public section


namespace SpectreGeometry
noncomputable section
open Set

theorem productPlacement_image_body (f g : ProductPlane ≃ᵢ ProductPlane) :
    productPlacement f g '' polygonProductBody =
      euclideanProductCoordinates '' ((f '' euclideanBody) ×ˢ (g '' euclideanBody)) := by
  rw [euclidean_product_body]
  ext z
  constructor
  · rintro ⟨_,⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩,rfl⟩
    exact ⟨(f x,g y),⟨⟨x,hx,rfl⟩,⟨y,hy,rfl⟩⟩,(productPlacement_apply f g x y).symm⟩
  · rintro ⟨⟨_,_⟩,⟨⟨x,hx,rfl⟩,⟨y,hy,rfl⟩⟩,rfl⟩
    exact ⟨euclideanProductCoordinates (x,y),⟨(x,y),⟨hx,hy⟩,rfl⟩,
      productPlacement_apply f g x y⟩

/-- Orthogonal products of genuine plane coverings cover all four-space. -/
theorem product_placements_cover {I J : Type*}
    (f : I → ProductPlane ≃ᵢ ProductPlane) (g : J → ProductPlane ≃ᵢ ProductPlane)
    (hf : ∀ x, ∃ i, x ∈ f i '' euclideanBody)
    (hg : ∀ y, ∃ j, y ∈ g j '' euclideanBody) :
    ∀ z : EFour, ∃ ij : I × J,
      z ∈ productPlacement (f ij.1) (g ij.2) '' polygonProductBody := by
  intro z
  obtain ⟨⟨x,y⟩,rfl⟩ := euclideanProductCoordinates.surjective z
  obtain ⟨i,hi⟩ := hf x
  obtain ⟨j,hj⟩ := hg y
  refine ⟨(i,j),?_⟩
  rw [productPlacement_image_body]
  exact ⟨(x,y),⟨hi,hj⟩,rfl⟩

/-- Orthogonal products preserve interior packing, with no boundary rule premise. -/
theorem product_placements_pack {I J : Type*}
    (f : I → ProductPlane ≃ᵢ ProductPlane) (g : J → ProductPlane ≃ᵢ ProductPlane)
    (hf : Pairwise fun i j => Disjoint (interior (f i '' euclideanBody))
      (interior (f j '' euclideanBody)))
    (hg : Pairwise fun i j => Disjoint (interior (g i '' euclideanBody))
      (interior (g j '' euclideanBody))) :
    Pairwise fun ij kl : I × J =>
      Disjoint (interior (productPlacement (f ij.1) (g ij.2) '' polygonProductBody))
        (interior (productPlacement (f kl.1) (g kl.2) '' polygonProductBody)) := by
  intro ij kl hne
  rw [productPlacement_image_body,productPlacement_image_body,
    ←euclideanProductCoordinates.image_interior,←euclideanProductCoordinates.image_interior,
    interior_prod_eq,interior_prod_eq]
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
  have he : x = y := euclideanProductCoordinates.injective (hxz.trans hyz.symm)
  subst y
  by_cases hi : ij.1 = kl.1
  · have hj : ij.2 ≠ kl.2 := by intro hj; exact hne (Prod.ext hi hj)
    exact Set.disjoint_left.mp (hg hj) hx.2 hy.2
  · exact Set.disjoint_left.mp (hf hi) hx.1 hy.1

end
end SpectreGeometry
