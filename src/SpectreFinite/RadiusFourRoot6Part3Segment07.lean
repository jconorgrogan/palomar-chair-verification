module

public import SpectreFinite.RadiusFourRoot6Part3Segment06
public import SpectreFinite.RadiusFourRoot6Part2
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable2
public import SpectreFinite.RadiusFourTable29
public import SpectreFinite.RadiusFourTable39
public import SpectreFinite.RadiusFourTable40

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
theorem root6Node10Step1Chunk7_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_3⟩
      root6Node10Domains0 root6Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node10Domains0 root6Node10Domains1
    root6Node10Domains0Fast root6Node10Domains1Fast
    root6Node10Domains0_fast_eq root6Node10Domains1_fast_eq (by decide)
theorem root6Node10Step1Chunk7_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_4⟩
      root6Node10Domains0 root6Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node10Domains0 root6Node10Domains1
    root6Node10Domains0Fast root6Node10Domains1Fast
    root6Node10Domains0_fast_eq root6Node10Domains1_fast_eq (by decide)
theorem root6Node10Step1Chunk7_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_5⟩
      root6Node10Domains0 root6Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node10Domains0 root6Node10Domains1
    root6Node10Domains0Fast root6Node10Domains1Fast
    root6Node10Domains0_fast_eq root6Node10Domains1_fast_eq (by decide)
theorem root6Node10Step1Chunk8_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_0⟩
      root6Node10Domains0 root6Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node10Domains0 root6Node10Domains1
    root6Node10Domains0Fast root6Node10Domains1Fast
    root6Node10Domains0_fast_eq root6Node10Domains1_fast_eq (by decide)
theorem root6Node10Step1Chunk8_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_1⟩
      root6Node10Domains0 root6Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node10Domains0 root6Node10Domains1
    root6Node10Domains0Fast root6Node10Domains1Fast
    root6Node10Domains0_fast_eq root6Node10Domains1_fast_eq (by decide)
theorem root6Node10Step1Chunk8_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_2⟩
      root6Node10Domains0 root6Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node10Domains0 root6Node10Domains1
    root6Node10Domains0Fast root6Node10Domains1Fast
    root6Node10Domains0_fast_eq root6Node10Domains1_fast_eq (by decide)
theorem root6Node10Step1Chunk8_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_3⟩
      root6Node10Domains0 root6Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node10Domains0 root6Node10Domains1
    root6Node10Domains0Fast root6Node10Domains1Fast
    root6Node10Domains0_fast_eq root6Node10Domains1_fast_eq (by decide)
theorem root6Node10Step1Chunk8_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_4⟩
      root6Node10Domains0 root6Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node10Domains0 root6Node10Domains1
    root6Node10Domains0Fast root6Node10Domains1Fast
    root6Node10Domains0_fast_eq root6Node10Domains1_fast_eq (by decide)
theorem root6Node10Step1Chunk8_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_5⟩
      root6Node10Domains0 root6Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node10Domains0 root6Node10Domains1
    root6Node10Domains0Fast root6Node10Domains1Fast
    root6Node10Domains0_fast_eq root6Node10Domains1_fast_eq (by decide)
theorem root6Node10Step1_checked :
    checkReplacement table29 root6Node10Domains0 root6Node10Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node10Step1Chunk0_0_checked, root6Node10Step1Chunk0_1_checked, root6Node10Step1Chunk0_2_checked, root6Node10Step1Chunk0_3_checked, root6Node10Step1Chunk0_4_checked, root6Node10Step1Chunk0_5_checked, root6Node10Step1Chunk1_0_checked, root6Node10Step1Chunk1_1_checked, root6Node10Step1Chunk1_2_checked, root6Node10Step1Chunk1_3_checked, root6Node10Step1Chunk1_4_checked, root6Node10Step1Chunk1_5_checked, root6Node10Step1Chunk2_0_checked, root6Node10Step1Chunk2_1_checked, root6Node10Step1Chunk2_2_checked, root6Node10Step1Chunk2_3_checked, root6Node10Step1Chunk2_4_checked, root6Node10Step1Chunk2_5_checked, root6Node10Step1Chunk3_0_checked, root6Node10Step1Chunk3_1_checked, root6Node10Step1Chunk3_2_checked, root6Node10Step1Chunk3_3_checked, root6Node10Step1Chunk3_4_checked, root6Node10Step1Chunk3_5_checked, root6Node10Step1Chunk4_0_checked, root6Node10Step1Chunk4_1_checked, root6Node10Step1Chunk4_2_checked, root6Node10Step1Chunk4_3_checked, root6Node10Step1Chunk4_4_checked, root6Node10Step1Chunk4_5_checked, root6Node10Step1Chunk5_0_checked, root6Node10Step1Chunk5_1_checked, root6Node10Step1Chunk5_2_checked, root6Node10Step1Chunk5_3_checked, root6Node10Step1Chunk5_4_checked, root6Node10Step1Chunk5_5_checked, root6Node10Step1Chunk6_0_checked, root6Node10Step1Chunk6_1_checked, root6Node10Step1Chunk6_2_checked, root6Node10Step1Chunk6_3_checked, root6Node10Step1Chunk6_4_checked, root6Node10Step1Chunk6_5_checked, root6Node10Step1Chunk7_0_checked, root6Node10Step1Chunk7_1_checked, root6Node10Step1Chunk7_2_checked, root6Node10Step1Chunk7_3_checked, root6Node10Step1Chunk7_4_checked, root6Node10Step1Chunk7_5_checked, root6Node10Step1Chunk8_0_checked, root6Node10Step1Chunk8_1_checked, root6Node10Step1Chunk8_2_checked, root6Node10Step1Chunk8_3_checked, root6Node10Step1Chunk8_4_checked, root6Node10Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node10Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4),(7,4),(8,4)]
  | 1 => [(0,0),(1,3),(6,3),(6,4)]
  | 2 => [(1,2),(7,2),(8,2)]
  | 3 => [(4,0),(5,0),(7,4),(8,0),(8,4)]
  | 4 => [(0,0),(1,3),(4,5),(7,3)]
  | 5 => [(4,1),(8,1)]
  | 6 => [(0,2),(1,5),(6,5)]
  | 7 => [(0,4),(1,1),(6,1)]
  | 8 => [(5,1),(5,4),(8,1)]
  | 9 => [(0,0),(0,1),(1,5),(6,4),(6,5)]
  | 10 => [(0,4),(1,2),(6,1),(6,2),(7,2)]
  | 11 => [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 12 => [(5,2),(5,5)]
  | 13 => [(7,0),(8,0)]
  | 14 => [(4,3),(8,3)]
  | 15 => [(1,5),(3,5),(5,5)]
  | 16 => [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 17 => [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 18 => [(0,1),(1,4),(6,5)]
  | 19 => [(0,4),(0,5),(6,2)]
  | 20 => [(4,4),(5,4),(8,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(2,0),(2,4),(4,4)]
  | 24 => [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 25 => [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 26 => [(2,5),(4,5),(7,5),(8,5)]
  | 27 => [(1,0),(6,0),(7,0)]
  | 28 => [(4,3),(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(3,1),(7,1)]
  | 32 => [(0,1),(1,5),(6,5),(7,5)]
  | 33 => [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 34 => [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 35 => [(7,2),(8,2)]
  | 36 => [(4,0),(7,4),(8,0)]
  | 37 => [(1,3),(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0),(8,0)]
  | 40 => [(4,5),(7,3)]
  | 41 => [(1,0),(4,2),(7,0),(8,2)]
  | 42 => [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 43 => [(5,1),(5,4),(8,1),(8,4)]
  | 44 => [(0,1),(6,4),(6,5)]
  | 45 => [(0,4),(1,2),(6,2)]
  | 46 => [(5,4),(8,4)]
  | 47 => [(0,0),(6,4)]
  | 48 => [(1,2),(7,2)]
  | 49 => [(4,0),(7,4),(8,4)]
  | 50 => [(5,5),(7,5),(8,5)]
  | 51 => [(0,3),(1,0),(7,0)]
  | 52 => [(4,3),(7,1),(8,1)]
  | 53 => [(1,5),(3,5),(7,5)]
  | 54 => [(0,3),(6,1)]
  | 55 => [(4,1),(5,1),(8,1)]
  | 56 => [(4,2),(4,4),(7,2),(8,2)]
  | 57 => [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 58 => [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 59 => [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | _ => [(1,3),(3,3),(5,3),(7,3),(8,3)]
def root6Node10Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4),(7,4),(8,4)]
  | 1 => some [(0,0),(1,3),(6,3),(6,4)]
  | 2 => some [(1,2),(7,2),(8,2)]
  | 3 => some [(4,0),(5,0),(7,4),(8,0),(8,4)]
  | 4 => some [(0,0),(1,3),(4,5),(7,3)]
  | 5 => some [(4,1),(8,1)]
  | 6 => some [(0,2),(1,5),(6,5)]
  | 7 => some [(0,4),(1,1),(6,1)]
  | 8 => some [(5,1),(5,4),(8,1)]
  | 9 => some [(0,0),(0,1),(1,5),(6,4),(6,5)]
  | 10 => some [(0,4),(1,2),(6,1),(6,2),(7,2)]
  | 11 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 12 => some [(5,2),(5,5)]
  | 13 => some [(7,0),(8,0)]
  | 14 => some [(4,3),(8,3)]
  | 15 => some [(1,5),(3,5),(5,5)]
  | 16 => some [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 17 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 18 => some [(0,1),(1,4),(6,5)]
  | 19 => some [(0,4),(0,5),(6,2)]
  | 20 => some [(4,4),(5,4),(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(2,0),(2,4),(4,4)]
  | 24 => some [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 25 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 26 => some [(2,5),(4,5),(7,5),(8,5)]
  | 27 => some [(1,0),(6,0),(7,0)]
  | 28 => some [(4,3),(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(3,1),(7,1)]
  | 32 => some [(0,1),(1,5),(6,5),(7,5)]
  | 33 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 34 => some [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(7,4),(8,0)]
  | 37 => some [(1,3),(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(1,0),(4,2),(7,0),(8,2)]
  | 42 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 43 => some [(5,1),(5,4),(8,1),(8,4)]
  | 44 => some [(0,1),(6,4),(6,5)]
  | 45 => some [(0,4),(1,2),(6,2)]
  | 46 => some [(5,4),(8,4)]
  | 47 => some [(0,0),(6,4)]
  | 48 => some [(1,2),(7,2)]
  | 49 => some [(4,0),(7,4),(8,4)]
  | 50 => some [(5,5),(7,5),(8,5)]
  | 51 => some [(0,3),(1,0),(7,0)]
  | 52 => some [(4,3),(7,1),(8,1)]
  | 53 => some [(1,5),(3,5),(7,5)]
  | 54 => some [(0,3),(6,1)]
  | 55 => some [(4,1),(5,1),(8,1)]
  | 56 => some [(4,2),(4,4),(7,2),(8,2)]
  | 57 => some [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 58 => some [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | _ => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
theorem root6Node10Domains2_fast_eq : root6Node10Domains2 = expandDomains root6Node10Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node10Domains2 v = expandDomains root6Node10Domains2Fast v from by decide) v
theorem root6Node10Step2Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root6Node10Domains1 root6Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node10Domains1 root6Node10Domains2
    root6Node10Domains1Fast root6Node10Domains2Fast
    root6Node10Domains1_fast_eq root6Node10Domains2_fast_eq (by decide)
theorem root6Node10Step2Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root6Node10Domains1 root6Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node10Domains1 root6Node10Domains2
    root6Node10Domains1Fast root6Node10Domains2Fast
    root6Node10Domains1_fast_eq root6Node10Domains2_fast_eq (by decide)
theorem root6Node10Step2Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root6Node10Domains1 root6Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node10Domains1 root6Node10Domains2
    root6Node10Domains1Fast root6Node10Domains2Fast
    root6Node10Domains1_fast_eq root6Node10Domains2_fast_eq (by decide)
theorem root6Node10Step2Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root6Node10Domains1 root6Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node10Domains1 root6Node10Domains2
    root6Node10Domains1Fast root6Node10Domains2Fast
    root6Node10Domains1_fast_eq root6Node10Domains2_fast_eq (by decide)
theorem root6Node10Step2Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root6Node10Domains1 root6Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node10Domains1 root6Node10Domains2
    root6Node10Domains1Fast root6Node10Domains2Fast
    root6Node10Domains1_fast_eq root6Node10Domains2_fast_eq (by decide)
theorem root6Node10Step2Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root6Node10Domains1 root6Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node10Domains1 root6Node10Domains2
    root6Node10Domains1Fast root6Node10Domains2Fast
    root6Node10Domains1_fast_eq root6Node10Domains2_fast_eq (by decide)
theorem root6Node10Step2Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root6Node10Domains1 root6Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node10Domains1 root6Node10Domains2
    root6Node10Domains1Fast root6Node10Domains2Fast
    root6Node10Domains1_fast_eq root6Node10Domains2_fast_eq (by decide)
theorem root6Node10Step2Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root6Node10Domains1 root6Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node10Domains1 root6Node10Domains2
    root6Node10Domains1Fast root6Node10Domains2Fast
    root6Node10Domains1_fast_eq root6Node10Domains2_fast_eq (by decide)
theorem root6Node10Step2Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root6Node10Domains1 root6Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node10Domains1 root6Node10Domains2
    root6Node10Domains1Fast root6Node10Domains2Fast
    root6Node10Domains1_fast_eq root6Node10Domains2_fast_eq (by decide)
theorem root6Node10Step2Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root6Node10Domains1 root6Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node10Domains1 root6Node10Domains2
    root6Node10Domains1Fast root6Node10Domains2Fast
    root6Node10Domains1_fast_eq root6Node10Domains2_fast_eq (by decide)
theorem root6Node10Step2Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root6Node10Domains1 root6Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node10Domains1 root6Node10Domains2
    root6Node10Domains1Fast root6Node10Domains2Fast
    root6Node10Domains1_fast_eq root6Node10Domains2_fast_eq (by decide)
theorem root6Node10Step2Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root6Node10Domains1 root6Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node10Domains1 root6Node10Domains2
    root6Node10Domains1Fast root6Node10Domains2Fast
    root6Node10Domains1_fast_eq root6Node10Domains2_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFour
