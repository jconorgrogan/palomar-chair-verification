module

public import SpectreClusters.StageDActualHierarchy

@[expose] public section


namespace SpectreClusters.StageD
open SpectreFinite SpectreFinite.HexSearch SpectreFinite.HexSearch.ParentOwnership

theorem actualClusterChart_direction (hD : FinalClusterCaptures)
    {f : Cell → ClusterPlacement} (hf : ValidClusterGridField f) (base : Cell)
    (v : Position) (d : Fin 6) :
    actualClusterChart hD hf base (addPos v (direction d)) =
      clusterStep finalRowChecks hD hf d (actualClusterChart hD hf base v) := by
  have he : addPos v (direction d) = addPos (direction d) v := by
    apply Prod.ext <;> simp only [addPos] <;> omega
  unfold actualClusterChart
  rw [he,HexStepSystem.translate_add,HexStepSystem.translate_direction]
  rfl

noncomputable def actualHierarchyBoundary (C : NativeHierarchy.ParentOccurrenceTheorem)
    (hD : FinalClusterCaptures) {f : Cell → ClusterPlacement}
    (hf : ValidClusterGridField f) (base : Cell) (n : Nat) (x : Position) :
    List (ActualCluster f × Fin 6) :=
  (NativeHierarchy.boundaryEdges C n (actualLegalField hD hf base) x).map
    (fun e => (actualClusterChart hD hf base e.1,e.2))

theorem actualHierarchyBoundary_bound (C : NativeHierarchy.ParentOccurrenceTheorem)
    (hD : FinalClusterCaptures) {f : Cell → ClusterPlacement}
    (hf : ValidClusterGridField f) (base : Cell) (n : Nat) (x : Position) :
    (actualHierarchyBoundary C hD hf base n x).length ≤ 6*6^n := by
  simpa only [actualHierarchyBoundary,List.length_map] using
    NativeHierarchy.boundaryEdges_bound C n (actualLegalField hD hf base) x

theorem actualHierarchyBoundary_cover (C : NativeHierarchy.ParentOccurrenceTheorem)
    (hD : FinalClusterCaptures) (hh : HaloOrderBinding) {f : Cell → ClusterPlacement}
    (hf : ValidClusterGridField f) (base : Cell) (n : Nat) (x : Position)
    (p : ActualCluster f) (d : Fin 6)
    (hp : p ∈ actualHierarchyBlock C hD hf base n x)
    (hout : clusterStep finalRowChecks hD hf d p ∉ actualHierarchyBlock C hD hf base n x) :
    (p,d) ∈ actualHierarchyBoundary C hD hf base n x := by
  obtain ⟨v,hv⟩ := actualClusterChart_surjective hD hh hf base p
  obtain ⟨u,hu,hup⟩ := List.mem_map.mp hp
  have huv := actualClusterChart_injective C hD hf base (hup.trans hv.symm)
  subst u
  have he : NativeBoundaryRefinement.Exposed
      (NativeHierarchy.blocks C n (actualLegalField hD hf base) x) (v,d) := by
    refine ⟨hu,?_⟩
    intro hin
    apply hout
    apply List.mem_map.mpr
    refine ⟨addPos v (direction d),hin,?_⟩
    rw [actualClusterChart_direction,hv]
  have hb := NativeHierarchy.boundaryEdges_cover C n (actualLegalField hD hf base) x (v,d) he
  exact List.mem_map.mpr ⟨(v,d),hb,Prod.ext hv rfl⟩

end SpectreClusters.StageD
