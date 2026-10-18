module

public import SpectreGeometry.PhysicalGridRootChange
public import SpectreClusters.DeformedParitySwap
public import SpectreClusters.StageAKindPresence

@[expose] public section


/-! Re-rooting at an actual old-frame hat reverses every literal tile kind.
The original physical tile index is retained throughout. -/
namespace SpectreGeometry
noncomputable section
open Set SpectreClusters SpectreClusters.DeformedLiteralBinding SpectreGeometry.Deformation
variable {ι : Type*} (f : ι → EPlane ≃ᵢ EPlane)
  (hdirect : ∀ i, DirectPlacement (f i))
  (hdisjoint : Pairwise fun i j =>
    Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
  (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody) (root : ι)

theorem tilingGridPlacement_root_change_kind (newroot i : ι)
    (hhat : (tilingGridPlacement f hdirect hdisjoint hcover root newroot).kind = .hat) :
    (tilingGridPlacement f hdirect hdisjoint hcover newroot i).kind =
      flipHTKind (tilingGridPlacement f hdirect hdisjoint hcover root i).kind := by
  change literalKind (tilingFrame f hdirect hdisjoint hcover newroot i) =
    flipHTKind (literalKind (tilingFrame f hdirect hdisjoint hcover root i))
  rw [tilingFrame_root_change_add f hdirect hdisjoint hcover root newroot i]
  exact literalKind_add_odd_flip _ _ hhat

theorem exists_hat_source (hcaptures : StageA.FinalCaptures) :
    ∃ newroot, (tilingGridPlacement f hdirect hdisjoint hcover root newroot).kind = .hat := by
  obtain ⟨p,hp,hkind⟩ := StageA.exists_owned_hat hcaptures
    (physicalGridField f hdirect hdisjoint hcover root)
    (physicalGridField_valid f hdirect hdisjoint hcover root)
  obtain ⟨i,hi⟩ := physicalGridField_owned_source f hdirect hdisjoint hcover root p hp
  exact ⟨i,hi ▸ hkind⟩

end
end SpectreGeometry
