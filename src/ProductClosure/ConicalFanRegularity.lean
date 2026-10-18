module

public import ProductClosure.GenericConicalFans
public import ProductClosure.CarrierConeRegularity

@[expose] public section

/-! Closedness of the actual finite-cell native conical fan. -/
namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace Topology
open Set
noncomputable section
variable {m : ℕ} {polyCells : Finset (Polycube.LatticeIndex (m + 1))}
variable [Nonempty (Polycube.Cell polyCells)]

/-- Every cone in the derived native shape classification is closed. -/
theorem ActualNativeCone.isClosed {J : ℕ} [NeZero m] {a : Coefficients polyCells J}
    {f : Space m ≃ᵢ Space m} {x : Space m} {C : Set (Space m)}
    (h : ActualNativeCone a f x C) : IsClosed C := by
  cases h with
  | strictSide u s hx hs => exact centeredHalfspace_isClosed _
  | base u s hx => exact twoHalfspaceCone_isClosed _ _ _
  | side u s t hst hx => exact twoHalfspaceCone_isClosed _ _ _
  | ordinary hx hkey => exact placedCarrierCone_isClosed _ _ _

theorem ActualTwoNormalGerm.cone_isClosed {J : ℕ} [NeZero m]
    {a : Coefficients polyCells J} {f : Space m ≃ᵢ Space m} {x p q : Space m}
    (G : ActualTwoNormalGerm a f x p q) : IsClosed G.cone :=
  G.native_shape.isClosed

#print axioms ActualNativeCone.isClosed
#print axioms placedActiveCarrierNormals_ne_zero

end
end ProductClosure.NativeCompiler
