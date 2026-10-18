module

public import SpectreClusters.StageDFinalChecks
public import SpectreClusters.StageDHTPeriod

@[expose] public section


/-! The actual-field recognizer with all inverse/triangle/mark/uniqueness law
checks discharged by the twenty kernel-checked row certificates. Only the
separate exhaustive capture and halo bindings remain explicit here. -/
namespace SpectreClusters.StageD
open SpectreFinite SpectreFinite.HexSearch SpectreFinite.HexSearch.ParentOwnership

theorem checked_cluster_period_gives_marked_period
    (hD : FinalClusterCaptures) (hh : HaloOrderBinding)
    (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (u : Point) (hne : u ≠ (0,0)) (hu : ClusterGridFieldTranslationPeriod f u) :
    ∃ F : Position → State, GloballyLegal F ∧
      ∃ v : Position, v ≠ (0,0) ∧ FieldPeriod F v :=
  periodic_cluster_field_gives_periodic_marked_field finalRowChecks hD hh f hf u hne hu

theorem checked_sparse_ht_period_gives_marked_period
    (hA : StageA.FinalCaptures) (hD : FinalClusterCaptures) (hh : HaloOrderBinding)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hs : StageA.SparseTurtles f)
    (u : Point) (hne : u ≠ (0,0)) (hu : GridFieldTranslationPeriod f u) :
    ∃ F : Position → State, GloballyLegal F ∧
      ∃ v : Position, v ≠ (0,0) ∧ FieldPeriod F v :=
  sparse_ht_period_gives_marked_period finalRowChecks hA hD hh f hf hs u hne hu

end SpectreClusters.StageD
