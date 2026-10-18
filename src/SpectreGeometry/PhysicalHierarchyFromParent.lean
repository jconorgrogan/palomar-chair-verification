module

public import SpectreGeometry.PhysicalHierarchyTransport
public import SpectreClusters.StageAFinalCaptureCertified
public import SpectreClusters.StageDReductionComplete
public import SpectreClusters.StageDRawCaptureComplete
public import SpectreClusters.StageDRawHaloBindingCertified

@[expose] public section


/-! Checked capture, reduction and halo instantiation of the homochiral
physical hierarchy. Only the exact ParentOccurrence theorem remains explicit. -/
namespace SpectreGeometry
noncomputable section
open Set SpectreClusters SpectreFinite SpectreFinite.HexSearch

variable (C : NativeHierarchy.ParentOccurrenceTheorem)
include C

/-- The same source-correct index blocks with the checked capture inputs supplied. -/
def physicalHierarchyIndicesFromParent {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody) (root : ι)
    (hs : StageA.SparseTurtles (physicalGridField f hdirect hdisjoint hcover root))
    (base : Cell) (n : Nat) (x : Position) : Set ι :=
  physicalHierarchyIndices C
    StageA.finalCaptures_certified
    (StageD.Reduction.finalClusterCaptures_of_raw StageD.Raw.rawCaptures_checked)
    f hdirect hdisjoint hcover root hs base n x

/-- Every homochiral physical P tiling has finite, uniquely covering and nested
 blocks of its original physical tile indices, with only the exact ParentOccurrence input remaining explicit. -/
theorem homochiral_physical_hierarchy_of_parent {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody) (base : Cell) :
    ∃ (root : ι) (hs : StageA.SparseTurtles (physicalGridField f hdirect hdisjoint hcover root)),
      (∀ n x, (physicalHierarchyIndicesFromParent C f hdirect hdisjoint hcover root hs base n x).Finite) ∧
      (∀ n i, ∃! x, i ∈ physicalHierarchyIndicesFromParent C f hdirect hdisjoint hcover root hs base n x) ∧
      (∀ n x, ∃ y,
        physicalHierarchyIndicesFromParent C f hdirect hdisjoint hcover root hs base n x ⊆
        physicalHierarchyIndicesFromParent C f hdirect hdisjoint hcover root hs base (n+1) y) :=
  homochiral_physical_hierarchy_of_certificates
    C StageA.finalCaptures_certified
    (StageD.Reduction.finalClusterCaptures_of_raw StageD.Raw.rawCaptures_checked)
    StageD.Raw.halo_interpretation_binding_certified f hdirect hdisjoint hcover base

/-- No nonzero carrier-collection translation preserves a homochiral physical P
 tiling, conditional on the retained ParentOccurrence theorem C. The remaining
 hypotheses describe the supplied ordinary physical tiling. -/
theorem homochiral_physical_period_eq_zero_of_parent {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody)
    (v : EPlane) (hperiod : Deformation.CarrierCollectionPeriod f v) : v = 0 :=
  homochiral_physical_period_eq_zero_of_certificates
    C StageA.finalCaptures_certified
    (StageD.Reduction.finalClusterCaptures_of_raw StageD.Raw.rawCaptures_checked)
    StageD.Raw.halo_interpretation_binding_certified f hdirect hdisjoint hcover v hperiod

end
end SpectreGeometry
