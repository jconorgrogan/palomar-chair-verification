module

public import SpectreFinite.RadiusFourRoot7Step1Chunk7_2Slice0
public import SpectreFinite.RadiusFourRoot7Step1Chunk7_2Slice1
public import SpectreFinite.RadiusFourRoot7Step1Chunk7_2Slice2
public import SpectreFinite.RadiusFourRoot7Step1Chunk7_2Slice3
public import SpectreFinite.RadiusFourRoot7Step1Chunk7_3Slice0
public import SpectreFinite.RadiusFourRoot7Step1Chunk7_3Slice1
public import SpectreFinite.RadiusFourRoot7Step1Chunk7_3Slice2
public import SpectreFinite.RadiusFourRoot7Step1Chunk7_3Slice3
public import SpectreFinite.RadiusFourRoot7Step1Chunk7_4Slice0
public import SpectreFinite.RadiusFourRoot7Step1Chunk7_4Slice1
public import SpectreFinite.RadiusFourRoot7Step1Chunk7_4Slice2
public import SpectreFinite.RadiusFourRoot7Step1Chunk7_4Slice3
public import SpectreFinite.RadiusFourRoot7Step1Chunk7_5Slice0
public import SpectreFinite.RadiusFourRoot7Step1Chunk7_5Slice1
public import SpectreFinite.RadiusFourRoot7Step1Chunk7_5Slice2
public import SpectreFinite.RadiusFourRoot7Step1Chunk7_5Slice3
public import SpectreFinite.RadiusFourRoot7Part0Segment01
public import SpectreFinite.RadiusFourRoot7Data
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable0
public import SpectreFinite.RadiusFourTable23
public import SpectreFinite.RadiusFourTable30
public import SpectreFinite.RadiusFourTable37
public import SpectreFinite.RadiusFourTable39

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
theorem root7Node0Step1Chunk7_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_2⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  rw [root7Node0Step1Chunk7_2_rows_exact]
  exact checkNarrowing_flatten table30Scope [RadiusThreePruning.stateRows7_2_0, RadiusThreePruning.stateRows7_2_1, RadiusThreePruning.stateRows7_2_2, RadiusThreePruning.stateRows7_2_3]
    root7Node0Domains0 root7Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node0Step1Chunk7_2_slice0_checked, root7Node0Step1Chunk7_2_slice1_checked, root7Node0Step1Chunk7_2_slice2_checked, root7Node0Step1Chunk7_2_slice3_checked, Bool.true_and])
theorem root7Node0Step1Chunk7_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_3⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  rw [root7Node0Step1Chunk7_3_rows_exact]
  exact checkNarrowing_flatten table30Scope [RadiusThreePruning.stateRows7_3_0, RadiusThreePruning.stateRows7_3_1, RadiusThreePruning.stateRows7_3_2, RadiusThreePruning.stateRows7_3_3]
    root7Node0Domains0 root7Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node0Step1Chunk7_3_slice0_checked, root7Node0Step1Chunk7_3_slice1_checked, root7Node0Step1Chunk7_3_slice2_checked, root7Node0Step1Chunk7_3_slice3_checked, Bool.true_and])
theorem root7Node0Step1Chunk7_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_4⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  rw [root7Node0Step1Chunk7_4_rows_exact]
  exact checkNarrowing_flatten table30Scope [RadiusThreePruning.stateRows7_4_0, RadiusThreePruning.stateRows7_4_1, RadiusThreePruning.stateRows7_4_2, RadiusThreePruning.stateRows7_4_3]
    root7Node0Domains0 root7Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node0Step1Chunk7_4_slice0_checked, root7Node0Step1Chunk7_4_slice1_checked, root7Node0Step1Chunk7_4_slice2_checked, root7Node0Step1Chunk7_4_slice3_checked, Bool.true_and])
theorem root7Node0Step1Chunk7_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_5⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  rw [root7Node0Step1Chunk7_5_rows_exact]
  exact checkNarrowing_flatten table30Scope [RadiusThreePruning.stateRows7_5_0, RadiusThreePruning.stateRows7_5_1, RadiusThreePruning.stateRows7_5_2, RadiusThreePruning.stateRows7_5_3]
    root7Node0Domains0 root7Node0Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node0Step1Chunk7_5_slice0_checked, root7Node0Step1Chunk7_5_slice1_checked, root7Node0Step1Chunk7_5_slice2_checked, root7Node0Step1Chunk7_5_slice3_checked, Bool.true_and])
theorem root7Node0Step1Chunk8_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_0⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk8_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_1⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk8_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_2⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk8_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_3⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk8_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_4⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1Chunk8_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_5⟩
      root7Node0Domains0 root7Node0Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains0 root7Node0Domains1
    root7Node0Domains0Fast root7Node0Domains1Fast
    root7Node0Domains0_fast_eq root7Node0Domains1_fast_eq (by decide)
theorem root7Node0Step1_checked :
    checkReplacement table30 root7Node0Domains0 root7Node0Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node0Step1Chunk0_0_checked, root7Node0Step1Chunk0_1_checked, root7Node0Step1Chunk0_2_checked, root7Node0Step1Chunk0_3_checked, root7Node0Step1Chunk0_4_checked, root7Node0Step1Chunk0_5_checked, root7Node0Step1Chunk1_0_checked, root7Node0Step1Chunk1_1_checked, root7Node0Step1Chunk1_2_checked, root7Node0Step1Chunk1_3_checked, root7Node0Step1Chunk1_4_checked, root7Node0Step1Chunk1_5_checked, root7Node0Step1Chunk2_0_checked, root7Node0Step1Chunk2_1_checked, root7Node0Step1Chunk2_2_checked, root7Node0Step1Chunk2_3_checked, root7Node0Step1Chunk2_4_checked, root7Node0Step1Chunk2_5_checked, root7Node0Step1Chunk3_0_checked, root7Node0Step1Chunk3_1_checked, root7Node0Step1Chunk3_2_checked, root7Node0Step1Chunk3_3_checked, root7Node0Step1Chunk3_4_checked, root7Node0Step1Chunk3_5_checked, root7Node0Step1Chunk4_0_checked, root7Node0Step1Chunk4_1_checked, root7Node0Step1Chunk4_2_checked, root7Node0Step1Chunk4_3_checked, root7Node0Step1Chunk4_4_checked, root7Node0Step1Chunk4_5_checked, root7Node0Step1Chunk5_0_checked, root7Node0Step1Chunk5_1_checked, root7Node0Step1Chunk5_2_checked, root7Node0Step1Chunk5_3_checked, root7Node0Step1Chunk5_4_checked, root7Node0Step1Chunk5_5_checked, root7Node0Step1Chunk6_0_checked, root7Node0Step1Chunk6_1_checked, root7Node0Step1Chunk6_2_checked, root7Node0Step1Chunk6_3_checked, root7Node0Step1Chunk6_4_checked, root7Node0Step1Chunk6_5_checked, root7Node0Step1Chunk7_0_checked, root7Node0Step1Chunk7_1_checked, root7Node0Step1Chunk7_2_checked, root7Node0Step1Chunk7_3_checked, root7Node0Step1Chunk7_4_checked, root7Node0Step1Chunk7_5_checked, root7Node0Step1Chunk8_0_checked, root7Node0Step1Chunk8_1_checked, root7Node0Step1Chunk8_2_checked, root7Node0Step1Chunk8_3_checked, root7Node0Step1Chunk8_4_checked, root7Node0Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node0Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => stateChoices
  | 1 => stateChoices
  | 2 => stateChoices
  | 3 => stateChoices
  | 4 => stateChoices
  | 5 => stateChoices
  | 6 => [(3,5),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 7 => [(0,3),(1,0),(3,0),(4,3),(5,0),(5,3),(8,3)]
  | 8 => [(2,1),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 9 => [(0,2),(0,3),(1,0),(6,0),(7,0)]
  | 10 => stateChoices
  | 11 => [(0,0),(0,1),(1,4),(6,3),(6,4)]
  | 12 => [(0,5),(1,2),(6,2),(7,2)]
  | 13 => [(2,4),(4,4),(7,4),(8,4)]
  | 14 => [(0,0),(1,3)]
  | 15 => [(3,2),(4,2),(5,2),(7,2),(8,2)]
  | 16 => [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 17 => stateChoices
  | 18 => [(0,2),(1,5),(7,5),(8,5)]
  | 19 => [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 20 => [(7,1),(8,1)]
  | 21 => [(1,5),(6,5)]
  | 22 => [(0,4),(6,1)]
  | 23 => [(3,4),(5,1),(5,4),(8,1)]
  | 24 => [(0,0),(0,1),(1,4),(6,3),(6,4),(6,5)]
  | 25 => stateChoices
  | 26 => [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 27 => [(4,2),(7,0),(8,0),(8,2)]
  | 28 => [(5,0),(5,3),(8,3)]
  | 29 => [(4,5),(5,5),(8,5)]
  | 30 => [(7,0)]
  | 31 => [(2,3),(4,3),(8,3)]
  | 32 => [(0,2),(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 33 => [(0,3),(1,0),(1,1),(3,0),(6,0),(6,1),(7,0)]
  | 34 => stateChoices
  | 35 => [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 36 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 37 => [(0,0),(0,5),(6,3)]
  | 38 => [(4,4),(7,2)]
  | 39 => [(1,4),(6,4),(7,4)]
  | 40 => [(0,5),(1,2),(1,3),(6,3)]
  | 41 => [(2,0),(2,2),(2,4),(4,0),(4,2),(4,4),(7,2),(8,2)]
  | 42 => stateChoices
  | 43 => [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(7,5),(8,1)]
  | 44 => [(0,2),(1,5),(6,0)]
  | 45 => [(1,1),(6,1),(7,1)]
  | 46 => [(4,1),(7,5),(8,1)]
  | 47 => [(0,2),(0,3),(6,0),(6,5)]
  | 48 => [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 49 => stateChoices
  | 50 => [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 51 => [(2,0),(4,0),(7,0),(8,0)]
  | 52 => [(7,3),(8,3)]
  | 53 => [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | 54 => [(3,0),(5,0),(5,3),(7,0),(8,0)]
  | 55 => stateChoices
  | 56 => [(3,1),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 57 => [(0,1),(1,4),(6,4),(7,4)]
  | 58 => [(0,5),(1,2),(6,2),(6,3)]
  | 59 => stateChoices
  | _ => stateChoices
def root7Node0Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => none
  | 1 => none
  | 2 => none
  | 3 => none
  | 4 => none
  | 5 => none
  | 6 => some [(3,5),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 7 => some [(0,3),(1,0),(3,0),(4,3),(5,0),(5,3),(8,3)]
  | 8 => some [(2,1),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 9 => some [(0,2),(0,3),(1,0),(6,0),(7,0)]
  | 10 => none
  | 11 => some [(0,0),(0,1),(1,4),(6,3),(6,4)]
  | 12 => some [(0,5),(1,2),(6,2),(7,2)]
  | 13 => some [(2,4),(4,4),(7,4),(8,4)]
  | 14 => some [(0,0),(1,3)]
  | 15 => some [(3,2),(4,2),(5,2),(7,2),(8,2)]
  | 16 => some [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 17 => none
  | 18 => some [(0,2),(1,5),(7,5),(8,5)]
  | 19 => some [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 20 => some [(7,1),(8,1)]
  | 21 => some [(1,5),(6,5)]
  | 22 => some [(0,4),(6,1)]
  | 23 => some [(3,4),(5,1),(5,4),(8,1)]
  | 24 => some [(0,0),(0,1),(1,4),(6,3),(6,4),(6,5)]
  | 25 => none
  | 26 => some [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 27 => some [(4,2),(7,0),(8,0),(8,2)]
  | 28 => some [(5,0),(5,3),(8,3)]
  | 29 => some [(4,5),(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(2,3),(4,3),(8,3)]
  | 32 => some [(0,2),(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 33 => some [(0,3),(1,0),(1,1),(3,0),(6,0),(6,1),(7,0)]
  | 34 => none
  | 35 => some [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 36 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 37 => some [(0,0),(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(6,4),(7,4)]
  | 40 => some [(0,5),(1,2),(1,3),(6,3)]
  | 41 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(4,4),(7,2),(8,2)]
  | 42 => none
  | 43 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(7,5),(8,1)]
  | 44 => some [(0,2),(1,5),(6,0)]
  | 45 => some [(1,1),(6,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(0,3),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 49 => none
  | 50 => some [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 51 => some [(2,0),(4,0),(7,0),(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | 54 => some [(3,0),(5,0),(5,3),(7,0),(8,0)]
  | 55 => none
  | 56 => some [(3,1),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 57 => some [(0,1),(1,4),(6,4),(7,4)]
  | 58 => some [(0,5),(1,2),(6,2),(6,3)]
  | 59 => none
  | _ => none
theorem root7Node0Domains2_fast_eq : root7Node0Domains2 = expandDomains root7Node0Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node0Domains2 v = expandDomains root7Node0Domains2Fast v from by decide) v
theorem root7Node0Step2Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
theorem root7Node0Step2Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root7Node0Domains1 root7Node0Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node0Domains1 root7Node0Domains2
    root7Node0Domains1Fast root7Node0Domains2Fast
    root7Node0Domains1_fast_eq root7Node0Domains2_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFour
