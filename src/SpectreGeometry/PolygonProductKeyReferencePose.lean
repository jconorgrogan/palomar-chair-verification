module

public import SpectreGeometry.PolygonProductKeyReferenceSeparation

@[expose] public section


namespace SpectreGeometry.ProductKeyReference
open SparseMonotiles
noncomputable section

/-- Coincident whole optimized reference keys determine both the absolute
label and the entire arbitrary Euclidean placement. -/
theorem placed_reference_unique (i j : Fin 2) (g h : Point 4 ≃ᵢ Point 4)
    (heq : g '' referenceSolid i = h '' referenceSolid j) : i = j ∧ g = h := by
  have hmap : (g.trans h.symm) '' referenceSolid i = referenceSolid j := by
    change (fun x => h.symm (g x)) '' referenceSolid i = referenceSolid j
    rw [←Set.image_image, heq]
    rw [Set.image_image]
    have hid : (fun x : Point 4 => h.symm (h x)) = id := funext h.symm_apply_apply
    rw [hid, Set.image_id]
  have hij := reference_label_of_isometric_image i j (g.trans h.symm) hmap
  refine ⟨hij,?_⟩
  subst j
  have hk := reference_isometry_stabilizer i (g.trans h.symm) hmap
  apply IsometryEquiv.ext
  intro x
  have hx := congrArg (fun e : Point 4 ≃ᵢ Point 4 => h (e x)) hk
  change h (h.symm (g x)) = h x at hx
  simpa only [IsometryEquiv.apply_symm_apply] using hx

end
end SpectreGeometry.ProductKeyReference
