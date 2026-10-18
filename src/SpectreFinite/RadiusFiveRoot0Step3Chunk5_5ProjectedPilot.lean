module

public import SpectreFinite.RadiusFiveRoot0Step3Chunk5_5ProjectedSlice0
public import SpectreFinite.RadiusFiveRoot0Step3Chunk5_5ProjectedSlice1
public import SpectreFinite.RadiusFiveRoot0Step3Chunk5_5ProjectedSlice2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
open HigherFastChecking
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root0Node0Step3Chunk5_5_projected_slices_pilot_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_5⟩
      root0Node0Domains2 root0Node0Domains3 = true := by
  rw [root0Node0Step3Chunk5_5_projected_rows_exact]
  exact checkNarrowing_flatten table33Scope [root0Node0Step3Chunk5_5_projectedRows0, root0Node0Step3Chunk5_5_projectedRows1, root0Node0Step3Chunk5_5_projectedRows2]
    root0Node0Domains2 root0Node0Domains3 (by
      simp only [List.all_cons, List.all_nil, root0Node0Step3Chunk5_5_projected_slice0_checked, root0Node0Step3Chunk5_5_projected_slice1_checked, root0Node0Step3Chunk5_5_projected_slice2_checked, Bool.true_and])

#print axioms root0Node0Step3Chunk5_5_projected_slices_pilot_checked
end SpectreFinite.HexSearch.RadiusFive
