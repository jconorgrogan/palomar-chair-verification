module

public import SpectreFinite.RadiusThreeRoot7Part36
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable19
public import SpectreFinite.RadiusThreeTable2
public import SpectreFinite.RadiusThreeTable4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node53Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(8,2)]
  | 8 => [(5,0),(8,0)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0),(6,4)]
  | 15 => [(4,2),(7,0),(8,0)]
  | 16 => [(5,3)]
  | 17 => [(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(1,5),(3,5),(7,5)]
  | 21 => [(0,3),(6,1)]
  | 22 => [(1,4),(3,4),(7,4)]
  | 23 => [(0,5),(6,3)]
  | 24 => [(4,4),(7,2)]
  | 25 => [(1,4),(7,4)]
  | 26 => [(0,5),(1,3),(6,3)]
  | 27 => [(2,0),(2,2),(2,4),(4,2)]
  | 28 => [(0,2),(6,0)]
  | 29 => [(1,1),(7,1)]
  | 30 => [(4,1),(7,5),(8,1)]
  | 31 => [(0,2),(6,0),(6,5)]
  | 32 => [(0,4),(1,1),(3,1),(7,1)]
  | 33 => [(4,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(5,2),(5,5),(8,2)]
  | _ => [(3,0),(5,0),(7,0)]
def root7Node53Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(8,2)]
  | 8 => some [(5,0),(8,0)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(0,0),(6,4)]
  | 15 => some [(4,2),(7,0),(8,0)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5),(3,5),(7,5)]
  | 21 => some [(0,3),(6,1)]
  | 22 => some [(1,4),(3,4),(7,4)]
  | 23 => some [(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(7,4)]
  | 26 => some [(0,5),(1,3),(6,3)]
  | 27 => some [(2,0),(2,2),(2,4),(4,2)]
  | 28 => some [(0,2),(6,0)]
  | 29 => some [(1,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(3,1),(7,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5),(8,2)]
  | _ => some [(3,0),(5,0),(7,0)]
theorem root7Node53Domains3_fast_eq : root7Node53Domains3 = expandDomains root7Node53Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node53Domains3 v = expandDomains root7Node53Domains3Fast v from by decide) v
theorem root7Node53Step3Chunk0_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_0⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk0_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_1⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk0_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_2⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk0_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_3⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk0_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_4⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk0_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_5⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk1_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_0⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk1_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_1⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk1_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_2⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk1_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_3⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk1_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_4⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk1_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_5⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk2_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_0⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk2_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_1⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk2_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_2⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk2_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_3⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk2_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_4⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk2_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_5⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk3_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_0⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk3_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_1⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk3_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_2⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk3_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_3⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk3_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_4⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk3_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_5⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk4_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_0⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk4_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_1⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk4_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_2⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk4_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_3⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk4_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_4⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk4_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_5⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk5_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_0⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk5_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_1⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk5_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_2⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk5_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_3⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk5_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_4⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk5_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_5⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk6_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_0⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk6_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_1⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk6_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_2⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk6_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_3⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk6_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_4⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk6_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_5⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk7_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_0⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk7_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_1⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk7_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_2⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk7_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_3⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk7_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_4⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk7_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_5⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk8_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_0⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk8_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_1⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk8_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_2⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk8_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_3⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk8_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_4⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3Chunk8_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_5⟩
      root7Node53Domains2 root7Node53Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains2 root7Node53Domains3
    root7Node53Domains2Fast root7Node53Domains3Fast
    root7Node53Domains2_fast_eq root7Node53Domains3_fast_eq (by decide)
theorem root7Node53Step3_checked :
    checkReplacement table2 root7Node53Domains2 root7Node53Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node53Step3Chunk0_0_checked, root7Node53Step3Chunk0_1_checked, root7Node53Step3Chunk0_2_checked, root7Node53Step3Chunk0_3_checked, root7Node53Step3Chunk0_4_checked, root7Node53Step3Chunk0_5_checked, root7Node53Step3Chunk1_0_checked, root7Node53Step3Chunk1_1_checked, root7Node53Step3Chunk1_2_checked, root7Node53Step3Chunk1_3_checked, root7Node53Step3Chunk1_4_checked, root7Node53Step3Chunk1_5_checked, root7Node53Step3Chunk2_0_checked, root7Node53Step3Chunk2_1_checked, root7Node53Step3Chunk2_2_checked, root7Node53Step3Chunk2_3_checked, root7Node53Step3Chunk2_4_checked, root7Node53Step3Chunk2_5_checked, root7Node53Step3Chunk3_0_checked, root7Node53Step3Chunk3_1_checked, root7Node53Step3Chunk3_2_checked, root7Node53Step3Chunk3_3_checked, root7Node53Step3Chunk3_4_checked, root7Node53Step3Chunk3_5_checked, root7Node53Step3Chunk4_0_checked, root7Node53Step3Chunk4_1_checked, root7Node53Step3Chunk4_2_checked, root7Node53Step3Chunk4_3_checked, root7Node53Step3Chunk4_4_checked, root7Node53Step3Chunk4_5_checked, root7Node53Step3Chunk5_0_checked, root7Node53Step3Chunk5_1_checked, root7Node53Step3Chunk5_2_checked, root7Node53Step3Chunk5_3_checked, root7Node53Step3Chunk5_4_checked, root7Node53Step3Chunk5_5_checked, root7Node53Step3Chunk6_0_checked, root7Node53Step3Chunk6_1_checked, root7Node53Step3Chunk6_2_checked, root7Node53Step3Chunk6_3_checked, root7Node53Step3Chunk6_4_checked, root7Node53Step3Chunk6_5_checked, root7Node53Step3Chunk7_0_checked, root7Node53Step3Chunk7_1_checked, root7Node53Step3Chunk7_2_checked, root7Node53Step3Chunk7_3_checked, root7Node53Step3Chunk7_4_checked, root7Node53Step3Chunk7_5_checked, root7Node53Step3Chunk8_0_checked, root7Node53Step3Chunk8_1_checked, root7Node53Step3Chunk8_2_checked, root7Node53Step3Chunk8_3_checked, root7Node53Step3Chunk8_4_checked, root7Node53Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node53Domains4 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(8,2)]
  | 8 => [(5,0),(8,0)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0),(6,4)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(1,5),(3,5),(7,5)]
  | 21 => [(0,3),(6,1)]
  | 22 => [(1,4),(3,4),(7,4)]
  | 23 => [(0,5),(6,3)]
  | 24 => [(4,4),(7,2)]
  | 25 => [(1,4),(7,4)]
  | 26 => [(0,5),(1,3),(6,3)]
  | 27 => [(2,0),(2,2),(2,4),(4,2)]
  | 28 => [(0,2),(6,0)]
  | 29 => [(1,1),(7,1)]
  | 30 => [(4,1),(7,5),(8,1)]
  | 31 => [(0,2),(6,0),(6,5)]
  | 32 => [(0,4),(1,1),(3,1),(7,1)]
  | 33 => [(4,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(5,2),(5,5),(8,2)]
  | _ => [(3,0),(5,0),(7,0)]
def root7Node53Domains4Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(8,2)]
  | 8 => some [(5,0),(8,0)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(0,0),(6,4)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5),(3,5),(7,5)]
  | 21 => some [(0,3),(6,1)]
  | 22 => some [(1,4),(3,4),(7,4)]
  | 23 => some [(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(7,4)]
  | 26 => some [(0,5),(1,3),(6,3)]
  | 27 => some [(2,0),(2,2),(2,4),(4,2)]
  | 28 => some [(0,2),(6,0)]
  | 29 => some [(1,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(3,1),(7,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5),(8,2)]
  | _ => some [(3,0),(5,0),(7,0)]
theorem root7Node53Domains4_fast_eq : root7Node53Domains4 = expandDomains root7Node53Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node53Domains4 v = expandDomains root7Node53Domains4Fast v from by decide) v
theorem root7Node53Step4Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root7Node53Domains3 root7Node53Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node53Domains3 root7Node53Domains4
    root7Node53Domains3Fast root7Node53Domains4Fast
    root7Node53Domains3_fast_eq root7Node53Domains4_fast_eq (by decide)
theorem root7Node53Step4_checked :
    checkReplacement table4 root7Node53Domains3 root7Node53Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node53Step4Chunk0_0_checked, root7Node53Step4Chunk0_1_checked, root7Node53Step4Chunk0_2_checked, root7Node53Step4Chunk0_3_checked, root7Node53Step4Chunk0_4_checked, root7Node53Step4Chunk0_5_checked, root7Node53Step4Chunk1_0_checked, root7Node53Step4Chunk1_1_checked, root7Node53Step4Chunk1_2_checked, root7Node53Step4Chunk1_3_checked, root7Node53Step4Chunk1_4_checked, root7Node53Step4Chunk1_5_checked, root7Node53Step4Chunk2_0_checked, root7Node53Step4Chunk2_1_checked, root7Node53Step4Chunk2_2_checked, root7Node53Step4Chunk2_3_checked, root7Node53Step4Chunk2_4_checked, root7Node53Step4Chunk2_5_checked, root7Node53Step4Chunk3_0_checked, root7Node53Step4Chunk3_1_checked, root7Node53Step4Chunk3_2_checked, root7Node53Step4Chunk3_3_checked, root7Node53Step4Chunk3_4_checked, root7Node53Step4Chunk3_5_checked, root7Node53Step4Chunk4_0_checked, root7Node53Step4Chunk4_1_checked, root7Node53Step4Chunk4_2_checked, root7Node53Step4Chunk4_3_checked, root7Node53Step4Chunk4_4_checked, root7Node53Step4Chunk4_5_checked, root7Node53Step4Chunk5_0_checked, root7Node53Step4Chunk5_1_checked, root7Node53Step4Chunk5_2_checked, root7Node53Step4Chunk5_3_checked, root7Node53Step4Chunk5_4_checked, root7Node53Step4Chunk5_5_checked, root7Node53Step4Chunk6_0_checked, root7Node53Step4Chunk6_1_checked, root7Node53Step4Chunk6_2_checked, root7Node53Step4Chunk6_3_checked, root7Node53Step4Chunk6_4_checked, root7Node53Step4Chunk6_5_checked, root7Node53Step4Chunk7_0_checked, root7Node53Step4Chunk7_1_checked, root7Node53Step4Chunk7_2_checked, root7Node53Step4Chunk7_3_checked, root7Node53Step4Chunk7_4_checked, root7Node53Step4Chunk7_5_checked, root7Node53Step4Chunk8_0_checked, root7Node53Step4Chunk8_1_checked, root7Node53Step4Chunk8_2_checked, root7Node53Step4Chunk8_3_checked, root7Node53Step4Chunk8_4_checked, root7Node53Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node54Domains0 : Domains 37 State := restrict root7Node53Domains4 8 (5,0)
def root7Node54Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(8,2)]
  | 8 => some [(5,0)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(0,0),(6,4)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5),(3,5),(7,5)]
  | 21 => some [(0,3),(6,1)]
  | 22 => some [(1,4),(3,4),(7,4)]
  | 23 => some [(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(7,4)]
  | 26 => some [(0,5),(1,3),(6,3)]
  | 27 => some [(2,0),(2,2),(2,4),(4,2)]
  | 28 => some [(0,2),(6,0)]
  | 29 => some [(1,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(3,1),(7,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5),(8,2)]
  | _ => some [(3,0),(5,0),(7,0)]
theorem root7Node54Domains0_fast_eq : root7Node54Domains0 = expandDomains root7Node54Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node54Domains0 v = expandDomains root7Node54Domains0Fast v from by decide) v
def root7Node54Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(8,2)]
  | 8 => [(5,0)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(0,0)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(1,5)]
  | 21 => [(6,1)]
  | 22 => [(1,4),(3,4),(7,4)]
  | 23 => [(0,5),(6,3)]
  | 24 => [(4,4)]
  | 25 => [(1,4)]
  | 26 => [(0,5)]
  | 27 => [(2,0)]
  | 28 => [(0,2),(6,0)]
  | 29 => [(1,1),(7,1)]
  | 30 => [(7,5)]
  | 31 => [(6,0)]
  | 32 => [(3,1)]
  | 33 => [(4,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(5,2),(5,5),(8,2)]
  | _ => [(3,0),(5,0),(7,0)]
def root7Node54Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(8,2)]
  | 8 => some [(5,0)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(0,0)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5)]
  | 21 => some [(6,1)]
  | 22 => some [(1,4),(3,4),(7,4)]
  | 23 => some [(0,5),(6,3)]
  | 24 => some [(4,4)]
  | 25 => some [(1,4)]
  | 26 => some [(0,5)]
  | 27 => some [(2,0)]
  | 28 => some [(0,2),(6,0)]
  | 29 => some [(1,1),(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(3,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5),(8,2)]
  | _ => some [(3,0),(5,0),(7,0)]
theorem root7Node54Domains1_fast_eq : root7Node54Domains1 = expandDomains root7Node54Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node54Domains1 v = expandDomains root7Node54Domains1Fast v from by decide) v
theorem root7Node54Step1Chunk0_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_0⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk0_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_1⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk0_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_2⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk0_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_3⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk0_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_4⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk0_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_5⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk1_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_0⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk1_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_1⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk1_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_2⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk1_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_3⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk1_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_4⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk1_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_5⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk2_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_0⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk2_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_1⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk2_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_2⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk2_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_3⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk2_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_4⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk2_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_5⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk3_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_0⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk3_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_1⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk3_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_2⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk3_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_3⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk3_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_4⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk3_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_5⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk4_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_0⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk4_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_1⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk4_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_2⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk4_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_3⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk4_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_4⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk4_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_5⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk5_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_0⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk5_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_1⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk5_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_2⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk5_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_3⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk5_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_4⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk5_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_5⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk6_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_0⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk6_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_1⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk6_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_2⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk6_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_3⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk6_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_4⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk6_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_5⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk7_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_0⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk7_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_1⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk7_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_2⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk7_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_3⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk7_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_4⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk7_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_5⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk8_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_0⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk8_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_1⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk8_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_2⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk8_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_3⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk8_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_4⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1Chunk8_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_5⟩
      root7Node54Domains0 root7Node54Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node54Domains0 root7Node54Domains1
    root7Node54Domains0Fast root7Node54Domains1Fast
    root7Node54Domains0_fast_eq root7Node54Domains1_fast_eq (by decide)
theorem root7Node54Step1_checked :
    checkReplacement table19 root7Node54Domains0 root7Node54Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node54Step1Chunk0_0_checked, root7Node54Step1Chunk0_1_checked, root7Node54Step1Chunk0_2_checked, root7Node54Step1Chunk0_3_checked, root7Node54Step1Chunk0_4_checked, root7Node54Step1Chunk0_5_checked, root7Node54Step1Chunk1_0_checked, root7Node54Step1Chunk1_1_checked, root7Node54Step1Chunk1_2_checked, root7Node54Step1Chunk1_3_checked, root7Node54Step1Chunk1_4_checked, root7Node54Step1Chunk1_5_checked, root7Node54Step1Chunk2_0_checked, root7Node54Step1Chunk2_1_checked, root7Node54Step1Chunk2_2_checked, root7Node54Step1Chunk2_3_checked, root7Node54Step1Chunk2_4_checked, root7Node54Step1Chunk2_5_checked, root7Node54Step1Chunk3_0_checked, root7Node54Step1Chunk3_1_checked, root7Node54Step1Chunk3_2_checked, root7Node54Step1Chunk3_3_checked, root7Node54Step1Chunk3_4_checked, root7Node54Step1Chunk3_5_checked, root7Node54Step1Chunk4_0_checked, root7Node54Step1Chunk4_1_checked, root7Node54Step1Chunk4_2_checked, root7Node54Step1Chunk4_3_checked, root7Node54Step1Chunk4_4_checked, root7Node54Step1Chunk4_5_checked, root7Node54Step1Chunk5_0_checked, root7Node54Step1Chunk5_1_checked, root7Node54Step1Chunk5_2_checked, root7Node54Step1Chunk5_3_checked, root7Node54Step1Chunk5_4_checked, root7Node54Step1Chunk5_5_checked, root7Node54Step1Chunk6_0_checked, root7Node54Step1Chunk6_1_checked, root7Node54Step1Chunk6_2_checked, root7Node54Step1Chunk6_3_checked, root7Node54Step1Chunk6_4_checked, root7Node54Step1Chunk6_5_checked, root7Node54Step1Chunk7_0_checked, root7Node54Step1Chunk7_1_checked, root7Node54Step1Chunk7_2_checked, root7Node54Step1Chunk7_3_checked, root7Node54Step1Chunk7_4_checked, root7Node54Step1Chunk7_5_checked, root7Node54Step1Chunk8_0_checked, root7Node54Step1Chunk8_1_checked, root7Node54Step1Chunk8_2_checked, root7Node54Step1Chunk8_3_checked, root7Node54Step1Chunk8_4_checked, root7Node54Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
