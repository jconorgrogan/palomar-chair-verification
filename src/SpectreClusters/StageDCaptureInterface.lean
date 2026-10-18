module

public import SpectreClusters.StageDFinalModel

@[expose] public section


/-! Exact remaining finite completeness obligation. The predicate is explicit
in all conditional final-row recognizers until the raw/reduction proof supplies
it. Its rows consist of actual owned cluster placements, not symbolic labels. -/
namespace SpectreClusters.StageD

def FinalClusterCaptures : Prop :=
  ∀ (f : Cell → ClusterPlacement), ValidClusterGridField f →
    ∀ (root : ClusterPlacement), ClusterRootOwned f root → LegalClusterKind root.kind →
      ∃ i : Row, rowKind i = root.kind ∧ ClusterPatchOwned f (movedPatch i root)

end SpectreClusters.StageD
