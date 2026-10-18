module

public import ProductClosure.NativeLatticeCells
public import ProductClosure.IntegralPoseAlgebra

@[expose] public section

/-! Literal lattice-cell centers in one actual key-companion component.
Reachability is generated only by whole physical key contacts. -/
namespace ProductClosure.NativeCompiler
open Set PhysicalRegistration
noncomputable section
variable {m : ℕ} {S : Finset (LatticeIndex m)}

theorem isometry_map_add_smul (f : Space m ≃ᵢ Space m)
    (x v : Space m) (r : ℝ) :
    f (x + r • v) = f x + r • placedNormal f v := by
  have h := affineIsometry_map_add f.toRealAffineIsometryEquiv x (r • v)
  simpa [placedNormal] using h

/-- A geometrically matched companion's inward cell is the root facet's
literal outward adjacent cell, at the level of actual placed centers. -/
theorem matched_companion_cellCenter (u v : Site S)
    (f g : Space m ≃ᵢ Space m)
    (ht : ∀ j, placedNormal g (siteAxis v j) = placedNormal f (siteAxis u j))
    (hn : placedNormal g (outward v.1) = -placedNormal f (outward u.1))
    (hc : f (siteCenter u) = g (siteCenter v)) :
    g (cellCenter (facetInsideCell v.1)) = f (latticeCenter (facetOutsideIndex u.1)) := by
  have hfacet : g (facetCenter v.1) = f (facetCenter u.1) := by
    have h := relativePlacement_facetCenter u v f g ht hc
    have hh := congrArg f h
    simpa [relativePlacement] using hh
  rw [facetInsideCell_center, facetOutsideIndex_center]
  rw [sub_eq_add_neg, ← neg_smul, isometry_map_add_smul, isometry_map_add_smul,
    hfacet, hn, smul_neg, neg_smul, neg_neg]


end
end ProductClosure.NativeCompiler
