module

public import SpectreClusters.StageDReductionGeometryChecks
public import SpectreClusters.StageDReductionHitChecks
public import SpectreClusters.StageDReductionStepChecks
public import SpectreClusters.StageDReductionCaptureBridge
public import SpectreClusters.StageDReductionRawBinding
public import SpectreClusters.StageDReductionFinalBinding

@[expose] public section


/-! All three exact owner-consistency rejection rounds, with original raw IDs.
Only the raw exhaustive capture theorem remains a premise in this assembly. -/
namespace SpectreClusters.StageD.Reduction

theorem captures_zero (hraw : Raw.RawCaptures) : Captures (tables.kept 0) :=
  raw_captures_compact hraw (fun k => (raw_row_count_binding k).symm) compact_raw_patch_binding

theorem actual_captures_three (hraw : Raw.RawCaptures) : Captures (tables.kept 3) :=
  captures_three tables tables_geometry_valid tables_hits_valid (captures_zero hraw) all_stages_checked

theorem finalClusterCaptures_of_raw (hraw : Raw.RawCaptures) : FinalClusterCaptures :=
  final_capture_of_compact (actual_captures_three hraw)

end SpectreClusters.StageD.Reduction
