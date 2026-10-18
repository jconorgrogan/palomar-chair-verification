module

public import SpectreFinite.RadiusFiveRoot0Part1Segment01
public import SpectreFinite.RadiusFiveRoot0Part0
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable34
public import SpectreFinite.RadiusFiveTable52
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
theorem root0Node0Step5Chunk7_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_5⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk8_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_0⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk8_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_1⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk8_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_2⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk8_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_3⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk8_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_4⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Chunk8_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_5⟩
      root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_of_fast _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq (by decide)
theorem root0Node0Step5Narrowing_checked :
    checkNarrowing table52 root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkNarrowing_flatten table52Scope [table52Rows0_0,table52Rows0_1,table52Rows0_2,table52Rows0_3,table52Rows0_4,table52Rows0_5,table52Rows1_0,table52Rows1_1,table52Rows1_2,table52Rows1_3,table52Rows1_4,table52Rows1_5,table52Rows2_0,table52Rows2_1,table52Rows2_2,table52Rows2_3,table52Rows2_4,table52Rows2_5,table52Rows3_0,table52Rows3_1,table52Rows3_2,table52Rows3_3,table52Rows3_4,table52Rows3_5,table52Rows4_0,table52Rows4_1,table52Rows4_2,table52Rows4_3,table52Rows4_4,table52Rows4_5,table52Rows5_0,table52Rows5_1,table52Rows5_2,table52Rows5_3,table52Rows5_4,table52Rows5_5,table52Rows6_0,table52Rows6_1,table52Rows6_2,table52Rows6_3,table52Rows6_4,table52Rows6_5,table52Rows7_0,table52Rows7_1,table52Rows7_2,table52Rows7_3,table52Rows7_4,table52Rows7_5,table52Rows8_0,table52Rows8_1,table52Rows8_2,table52Rows8_3,table52Rows8_4,table52Rows8_5]
    root0Node0Domains4 root0Node0Domains5 (by
      simp only [List.all_cons, List.all_nil, root0Node0Step5Chunk0_0_checked, root0Node0Step5Chunk0_1_checked, root0Node0Step5Chunk0_2_checked, root0Node0Step5Chunk0_3_checked, root0Node0Step5Chunk0_4_checked, root0Node0Step5Chunk0_5_checked, root0Node0Step5Chunk1_0_checked, root0Node0Step5Chunk1_1_checked, root0Node0Step5Chunk1_2_checked, root0Node0Step5Chunk1_3_checked, root0Node0Step5Chunk1_4_checked, root0Node0Step5Chunk1_5_checked, root0Node0Step5Chunk2_0_checked, root0Node0Step5Chunk2_1_checked, root0Node0Step5Chunk2_2_checked, root0Node0Step5Chunk2_3_checked, root0Node0Step5Chunk2_4_checked, root0Node0Step5Chunk2_5_checked, root0Node0Step5Chunk3_0_checked, root0Node0Step5Chunk3_1_checked, root0Node0Step5Chunk3_2_checked, root0Node0Step5Chunk3_3_checked, root0Node0Step5Chunk3_4_checked, root0Node0Step5Chunk3_5_checked, root0Node0Step5Chunk4_0_checked, root0Node0Step5Chunk4_1_checked, root0Node0Step5Chunk4_2_checked, root0Node0Step5Chunk4_3_checked, root0Node0Step5Chunk4_4_checked, root0Node0Step5Chunk4_5_checked, root0Node0Step5Chunk5_0_checked, root0Node0Step5Chunk5_1_checked, root0Node0Step5Chunk5_2_checked, root0Node0Step5Chunk5_3_checked, root0Node0Step5Chunk5_4_checked, root0Node0Step5Chunk5_5_checked, root0Node0Step5Chunk6_0_checked, root0Node0Step5Chunk6_1_checked, root0Node0Step5Chunk6_2_checked, root0Node0Step5Chunk6_3_checked, root0Node0Step5Chunk6_4_checked, root0Node0Step5Chunk6_5_checked, root0Node0Step5Chunk7_0_checked, root0Node0Step5Chunk7_1_checked, root0Node0Step5Chunk7_2_checked, root0Node0Step5Chunk7_3_checked, root0Node0Step5Chunk7_4_checked, root0Node0Step5Chunk7_5_checked, root0Node0Step5Chunk8_0_checked, root0Node0Step5Chunk8_1_checked, root0Node0Step5Chunk8_2_checked, root0Node0Step5Chunk8_3_checked, root0Node0Step5Chunk8_4_checked, root0Node0Step5Chunk8_5_checked, Bool.true_and])
theorem root0Node0Step5_checked :
    checkReplacement table52 root0Node0Domains4 root0Node0Domains5 = true := by
  exact checkReplacement_of_fast_rest _ root0Node0Domains4 root0Node0Domains5
    root0Node0Domains4Fast root0Node0Domains5Fast
    root0Node0Domains4_fast_eq root0Node0Domains5_fast_eq
    root0Node0Step5Narrowing_checked (by decide)
def root0Node1Domains0 : Domains 91 State := restrict root0Node0Domains5 46 (3,2)
def root0Node1Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 1 => some [(0,4),(1,1),(6,1),(6,2),(7,1)]
  | 2 => some [(4,1),(5,1),(5,4),(7,5),(8,1),(8,4)]
  | 3 => some [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 4 => some [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 5 => some [(0,1),(1,4),(1,5),(6,5),(7,4),(8,4)]
  | 6 => some [(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,5)]
  | 7 => some [(1,0),(4,0),(7,0),(8,0)]
  | 8 => some [(4,3),(7,1),(7,3),(8,3)]
  | 9 => some [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 10 => some [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 11 => some [(2,1),(2,5),(4,1),(4,5),(8,1)]
  | 12 => some [(0,2),(1,0),(1,5),(6,0),(6,5),(7,0)]
  | 13 => some [(0,0),(0,3),(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 14 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 15 => some [(0,1),(1,4),(4,0),(7,4)]
  | 16 => some [(0,5),(1,3),(6,2),(6,3),(7,3)]
  | 17 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(8,4)]
  | 18 => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 19 => some [(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 20 => some [(4,0),(7,0),(7,4),(8,0)]
  | 21 => some [(0,2),(1,0),(1,5),(4,2),(6,0),(7,0)]
  | 22 => some [(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 23 => some [(4,1),(5,1),(7,5),(8,1),(8,5)]
  | 24 => some [(0,1),(0,2),(1,0),(6,0),(6,5)]
  | 25 => some [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 26 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 27 => some [(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 28 => some [(4,4),(5,1),(5,4),(7,2),(8,1),(8,4)]
  | 29 => some [(0,1),(1,4),(6,4),(6,5),(7,4)]
  | 30 => some [(1,2),(3,2),(5,2),(5,5),(7,2),(8,2)]
  | 31 => some [(4,0),(7,0),(7,4),(8,0)]
  | 32 => some [(1,3),(7,3),(8,3)]
  | 33 => some [(5,2),(5,5),(8,2)]
  | 34 => some [(1,0),(3,0),(5,0)]
  | 35 => some [(2,1),(2,5),(4,5)]
  | 36 => some [(0,2),(1,0),(6,0),(7,0)]
  | 37 => some [(1,1),(4,3),(7,1),(8,3)]
  | 38 => some [(4,1),(7,5),(8,5)]
  | 39 => some [(0,2),(0,3),(1,0),(6,0),(7,0)]
  | 40 => some [(0,3),(0,4),(0,5),(1,1),(6,1),(6,2)]
  | 41 => some [(4,4),(5,1),(5,4),(8,1),(8,4)]
  | 42 => some [(0,1),(1,4),(6,4),(6,5)]
  | 43 => some [(0,4),(0,5),(1,2),(6,2)]
  | 44 => some [(4,4),(5,4),(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(3,2)]
  | 47 => some [(4,0),(7,4)]
  | 48 => some [(1,3),(6,3),(7,3)]
  | 49 => some [(4,2),(5,2),(7,2),(8,2)]
  | 50 => some [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 51 => some [(4,3),(5,3),(7,1),(8,3)]
  | 52 => some [(5,5),(7,5),(8,5)]
  | 53 => some [(0,3),(1,0),(6,0),(7,0)]
  | 54 => some [(4,3),(7,1),(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(4,1),(5,1),(8,1)]
  | 58 => some [(0,1),(0,2),(6,5)]
  | 59 => some [(0,4),(1,1),(6,2)]
  | 60 => some [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(8,1),(8,4)]
  | 61 => some [(0,5),(1,3),(7,3)]
  | 62 => some [(4,2),(4,4),(8,2)]
  | 63 => some [(1,4),(5,0),(5,3)]
  | 64 => some [(0,5),(4,5),(5,5),(8,5)]
  | 65 => some [(2,0),(7,0)]
  | 66 => some [(7,3),(8,3)]
  | 67 => some [(5,2),(5,5),(8,5)]
  | 68 => some [(1,0),(3,0),(7,0),(8,0)]
  | 69 => some [(2,1),(2,3),(2,5),(4,3),(7,1),(7,3),(8,3)]
  | 70 => some [(0,4),(1,2),(6,2),(7,1)]
  | 71 => some [(1,4),(3,4),(5,4),(7,4),(7,5),(8,4)]
  | 72 => some [(0,0),(0,5),(6,0),(6,3)]
  | 73 => some [(3,1),(4,4),(7,2)]
  | 74 => some [(0,1),(1,4),(7,4)]
  | 75 => some [(0,5),(1,3),(6,2),(6,3)]
  | 76 => some [(4,4),(7,2),(8,2),(8,4)]
  | 77 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 78 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(7,3),(8,1)]
  | 79 => some [(0,2),(1,5),(6,0),(8,2)]
  | 80 => some [(1,1),(5,0),(6,1),(7,1)]
  | 81 => some [(4,1),(4,5),(7,5),(8,1)]
  | 82 => some [(0,2),(1,0),(6,0),(6,5)]
  | 83 => some [(0,4),(1,1),(7,1)]
  | 84 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 85 => some [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(6,2),(7,2),(8,5)]
  | 86 => some [(2,0),(4,0),(7,0),(8,0),(8,4)]
  | 87 => some [(0,0),(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 89 => some [(4,0),(5,0),(7,0),(8,0)]
  | _ => some [(4,3),(4,5),(7,3),(8,3)]
theorem root0Node1Domains0_fast_eq : root0Node1Domains0 = expandDomains root0Node1Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node1Domains0 v = expandDomains root0Node1Domains0Fast v from by decide) v
def root0Node1Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(0,1),(1,4),(1,5),(6,5),(7,4),(8,4)]
  | 6 => [(4,5),(8,5)]
  | 7 => [(1,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(0,3)]
  | 11 => [(8,1)]
  | 12 => [(0,2),(1,0),(1,5),(6,0),(6,5),(7,0)]
  | 13 => [(0,0),(6,3)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(4,2)]
  | 18 => [(5,3)]
  | 19 => [(8,5)]
  | 20 => [(4,0),(7,0),(7,4),(8,0)]
  | 21 => [(0,2),(1,5)]
  | 22 => [(1,1),(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(7,4)]
  | 27 => [(6,3)]
  | 28 => [(7,2)]
  | 29 => [(0,1),(1,4),(6,4),(6,5),(7,4)]
  | 30 => [(5,2),(5,5)]
  | 31 => [(7,0),(8,0)]
  | 32 => [(8,3)]
  | 33 => [(5,5)]
  | 34 => [(1,0)]
  | 35 => [(2,1)]
  | 36 => [(0,2)]
  | 37 => [(1,1)]
  | 38 => [(4,1)]
  | 39 => [(0,2),(0,3),(1,0),(6,0),(7,0)]
  | 40 => [(0,3),(0,4),(0,5),(1,1),(6,1),(6,2)]
  | 41 => [(4,4),(5,4),(8,4)]
  | 42 => [(1,4)]
  | 43 => [(0,5)]
  | 44 => [(4,4)]
  | 45 => [(0,0)]
  | 46 => [(3,2)]
  | 47 => [(4,0)]
  | 48 => [(7,3)]
  | 49 => [(4,2),(5,2),(7,2),(8,2)]
  | 50 => [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 51 => [(4,3),(5,3),(7,1),(8,3)]
  | 52 => [(7,5)]
  | 53 => [(6,0)]
  | 54 => [(7,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(5,1)]
  | 58 => [(0,1)]
  | 59 => [(0,4),(1,1),(6,2)]
  | 60 => [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(8,1),(8,4)]
  | 61 => [(0,5),(1,3),(7,3)]
  | 62 => [(8,2)]
  | 63 => [(5,0)]
  | 64 => [(4,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(8,5)]
  | 68 => [(1,0),(3,0),(7,0),(8,0)]
  | 69 => [(2,1),(2,3),(2,5),(4,3),(7,1),(7,3),(8,3)]
  | 70 => [(0,4),(1,2),(6,2),(7,1)]
  | 71 => [(5,4),(8,4)]
  | 72 => [(0,0)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(1,3),(6,3)]
  | 76 => [(4,4),(7,2),(8,2),(8,4)]
  | 77 => [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 78 => [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(7,3),(8,1)]
  | 79 => [(0,2),(1,5),(6,0),(8,2)]
  | 80 => [(1,1),(5,0),(6,1),(7,1)]
  | 81 => [(4,1),(4,5),(7,5),(8,1)]
  | 82 => [(0,2),(1,0),(6,0),(6,5)]
  | 83 => [(0,4),(1,1),(7,1)]
  | 84 => [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 85 => [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(6,2),(7,2),(8,5)]
  | 86 => [(2,0),(4,0),(7,0),(8,0),(8,4)]
  | 87 => [(0,0),(7,3),(8,3)]
  | 88 => [(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 89 => [(4,0),(5,0),(7,0),(8,0)]
  | _ => [(4,3),(4,5),(7,3),(8,3)]
def root0Node1Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(0,1),(1,4),(1,5),(6,5),(7,4),(8,4)]
  | 6 => some [(4,5),(8,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(8,1)]
  | 12 => some [(0,2),(1,0),(1,5),(6,0),(6,5),(7,0)]
  | 13 => some [(0,0),(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(4,2)]
  | 18 => some [(5,3)]
  | 19 => some [(8,5)]
  | 20 => some [(4,0),(7,0),(7,4),(8,0)]
  | 21 => some [(0,2),(1,5)]
  | 22 => some [(1,1),(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,4)]
  | 27 => some [(6,3)]
  | 28 => some [(7,2)]
  | 29 => some [(0,1),(1,4),(6,4),(6,5),(7,4)]
  | 30 => some [(5,2),(5,5)]
  | 31 => some [(7,0),(8,0)]
  | 32 => some [(8,3)]
  | 33 => some [(5,5)]
  | 34 => some [(1,0)]
  | 35 => some [(2,1)]
  | 36 => some [(0,2)]
  | 37 => some [(1,1)]
  | 38 => some [(4,1)]
  | 39 => some [(0,2),(0,3),(1,0),(6,0),(7,0)]
  | 40 => some [(0,3),(0,4),(0,5),(1,1),(6,1),(6,2)]
  | 41 => some [(4,4),(5,4),(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(0,5)]
  | 44 => some [(4,4)]
  | 45 => some [(0,0)]
  | 46 => some [(3,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(4,2),(5,2),(7,2),(8,2)]
  | 50 => some [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 51 => some [(4,3),(5,3),(7,1),(8,3)]
  | 52 => some [(7,5)]
  | 53 => some [(6,0)]
  | 54 => some [(7,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(0,4),(1,1),(6,2)]
  | 60 => some [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(8,1),(8,4)]
  | 61 => some [(0,5),(1,3),(7,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0),(3,0),(7,0),(8,0)]
  | 69 => some [(2,1),(2,3),(2,5),(4,3),(7,1),(7,3),(8,3)]
  | 70 => some [(0,4),(1,2),(6,2),(7,1)]
  | 71 => some [(5,4),(8,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3),(6,3)]
  | 76 => some [(4,4),(7,2),(8,2),(8,4)]
  | 77 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 78 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(7,3),(8,1)]
  | 79 => some [(0,2),(1,5),(6,0),(8,2)]
  | 80 => some [(1,1),(5,0),(6,1),(7,1)]
  | 81 => some [(4,1),(4,5),(7,5),(8,1)]
  | 82 => some [(0,2),(1,0),(6,0),(6,5)]
  | 83 => some [(0,4),(1,1),(7,1)]
  | 84 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 85 => some [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(6,2),(7,2),(8,5)]
  | 86 => some [(2,0),(4,0),(7,0),(8,0),(8,4)]
  | 87 => some [(0,0),(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 89 => some [(4,0),(5,0),(7,0),(8,0)]
  | _ => some [(4,3),(4,5),(7,3),(8,3)]
theorem root0Node1Domains1_fast_eq : root0Node1Domains1 = expandDomains root0Node1Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node1Domains1 v = expandDomains root0Node1Domains1Fast v from by decide) v
theorem root0Node1Step1Chunk0_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_0⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk0_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_1⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk0_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_2⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk0_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_3⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk0_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_4⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk0_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_5⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk1_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_0⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk1_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_1⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk1_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_2⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
theorem root0Node1Step1Chunk1_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_3⟩
      root0Node1Domains0 root0Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains0 root0Node1Domains1
    root0Node1Domains0Fast root0Node1Domains1Fast
    root0Node1Domains0_fast_eq root0Node1Domains1_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFive
