module

public import SpectreClusters.StageDReductionModel

@[expose] public section


/-! Linear-time raw-row hit checking, avoiding repeated long-list indexing. -/
namespace SpectreClusters.StageD.Reduction

def allRawHitCheckB (k : ClusterKind) (mask : Nat) : Bool :=
  (compactRowIDs k).all fun ids => ids.any fun m =>
    decide (m < (compactCandidates k).length) && mask.testBit m

theorem hitCheckB_of_all_raw (kept : Nat → ClusterKind → List Nat) (g : HitGroup)
    (hb : ∀ i ∈ kept g.stage g.kind, i < (compactRowIDs g.kind).length)
    (h : allRawHitCheckB g.kind g.mask = true) : hitCheckB kept g = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hbound := hb i hi
  have hm : compactIDs g.kind i ∈ compactRowIDs g.kind := by
    simpa [compactIDs,List.getD_eq_getElem?_getD,hbound] using (List.getElem_mem hbound)
  exact List.all_eq_true.mp h _ hm

end SpectreClusters.StageD.Reduction
