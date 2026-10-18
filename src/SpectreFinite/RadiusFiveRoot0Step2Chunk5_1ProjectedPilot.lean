module

public import SpectreFinite.RadiusFiveRoot0Step2Chunk5_1ProjectedSlice0
public import SpectreFinite.RadiusFiveRoot0Step2Chunk5_1ProjectedSlice1
public import SpectreFinite.RadiusFiveRoot0Step2Chunk5_1ProjectedSlice2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
open HigherFastChecking
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root0Node0Step2Chunk5_1_projected_slices_pilot_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root0Node0Domains1 root0Node0Domains2 = true := by
  rw [root0Node0Step2Chunk5_1_projected_rows_exact]
  exact checkNarrowing_flatten table57Scope [root0Node0Step2Chunk5_1_projectedRows0, root0Node0Step2Chunk5_1_projectedRows1, root0Node0Step2Chunk5_1_projectedRows2]
    root0Node0Domains1 root0Node0Domains2 (by
      simp only [List.all_cons, List.all_nil, root0Node0Step2Chunk5_1_projected_slice0_checked, root0Node0Step2Chunk5_1_projected_slice1_checked, root0Node0Step2Chunk5_1_projected_slice2_checked, Bool.true_and])

#print axioms root0Node0Step2Chunk5_1_projected_slices_pilot_checked
end SpectreFinite.HexSearch.RadiusFive
