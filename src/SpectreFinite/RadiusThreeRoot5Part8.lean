module

public import SpectreFinite.RadiusThreeRoot5Part7
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable0
public import SpectreFinite.RadiusThreeTable1
public import SpectreFinite.RadiusThreeTable24

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node12Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0),(8,0)]
  | 1 => [(4,3),(8,3)]
  | 2 => [(1,5),(3,5),(5,5),(7,5)]
  | 3 => [(0,3),(1,0),(3,0),(6,1)]
  | 4 => [(4,4),(7,2),(8,4)]
  | 5 => [(1,4),(7,4)]
  | 6 => [(0,5),(6,3)]
  | 7 => [(2,0),(2,2),(2,4),(4,4)]
  | 8 => [(0,0),(1,3),(3,3),(7,3)]
  | 9 => [(1,1),(6,1),(7,1)]
  | 10 => [(4,1),(7,5)]
  | 11 => [(0,2),(6,0)]
  | 12 => [(1,1),(3,1),(7,1)]
  | 13 => [(0,1),(1,5),(6,5)]
  | 14 => [(0,4),(6,1),(6,2)]
  | 15 => [(4,0),(7,0),(8,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2),(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(1,0),(7,0)]
  | 21 => [(4,3),(7,1),(8,3)]
  | 22 => [(0,1),(6,4)]
  | 23 => [(1,2),(6,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(0,3),(1,0)]
  | 29 => [(7,1),(8,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(4,1),(5,1),(8,1)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5),(5,5),(8,5)]
  | 35 => [(2,0),(7,0)]
  | _ => [(7,3),(8,3)]
def root5Node12Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0),(8,0)]
  | 1 => some [(4,3),(8,3)]
  | 2 => some [(1,5),(3,5),(5,5),(7,5)]
  | 3 => some [(0,3),(1,0),(3,0),(6,1)]
  | 4 => some [(4,4),(7,2),(8,4)]
  | 5 => some [(1,4),(7,4)]
  | 6 => some [(0,5),(6,3)]
  | 7 => some [(2,0),(2,2),(2,4),(4,4)]
  | 8 => some [(0,0),(1,3),(3,3),(7,3)]
  | 9 => some [(1,1),(6,1),(7,1)]
  | 10 => some [(4,1),(7,5)]
  | 11 => some [(0,2),(6,0)]
  | 12 => some [(1,1),(3,1),(7,1)]
  | 13 => some [(0,1),(1,5),(6,5)]
  | 14 => some [(0,4),(6,1),(6,2)]
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2),(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0),(7,0)]
  | 21 => some [(4,3),(7,1),(8,3)]
  | 22 => some [(0,1),(6,4)]
  | 23 => some [(1,2),(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(0,3),(1,0)]
  | 29 => some [(7,1),(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1),(5,1),(8,1)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(5,5),(8,5)]
  | 35 => some [(2,0),(7,0)]
  | _ => some [(7,3),(8,3)]
theorem root5Node12Domains3_fast_eq : root5Node12Domains3 = expandDomains root5Node12Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node12Domains3 v = expandDomains root5Node12Domains3Fast v from by decide) v
theorem root5Node12Step3Chunk0_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_0⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk0_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_1⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk0_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_2⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk0_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_3⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk0_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_4⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk0_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_5⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk1_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_0⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk1_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_1⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk1_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_2⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk1_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_3⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk1_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_4⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk1_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_5⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk2_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_0⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk2_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_1⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk2_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_2⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk2_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_3⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk2_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_4⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk2_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_5⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk3_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_0⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk3_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_1⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk3_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_2⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk3_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_3⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk3_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_4⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk3_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_5⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk4_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_0⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk4_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_1⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk4_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_2⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk4_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_3⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk4_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_4⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk4_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_5⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk5_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_0⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk5_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_1⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk5_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_2⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk5_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_3⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk5_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_4⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk5_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_5⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk6_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_0⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk6_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_1⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk6_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_2⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk6_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_3⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk6_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_4⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk6_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_5⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk7_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_0⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk7_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_1⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk7_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_2⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk7_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_3⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk7_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_4⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk7_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_5⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk8_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_0⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk8_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_1⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk8_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_2⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk8_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_3⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk8_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_4⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3Chunk8_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_5⟩
      root5Node12Domains2 root5Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains2 root5Node12Domains3
    root5Node12Domains2Fast root5Node12Domains3Fast
    root5Node12Domains2_fast_eq root5Node12Domains3_fast_eq (by decide)
theorem root5Node12Step3_checked :
    checkReplacement table1 root5Node12Domains2 root5Node12Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node12Step3Chunk0_0_checked, root5Node12Step3Chunk0_1_checked, root5Node12Step3Chunk0_2_checked, root5Node12Step3Chunk0_3_checked, root5Node12Step3Chunk0_4_checked, root5Node12Step3Chunk0_5_checked, root5Node12Step3Chunk1_0_checked, root5Node12Step3Chunk1_1_checked, root5Node12Step3Chunk1_2_checked, root5Node12Step3Chunk1_3_checked, root5Node12Step3Chunk1_4_checked, root5Node12Step3Chunk1_5_checked, root5Node12Step3Chunk2_0_checked, root5Node12Step3Chunk2_1_checked, root5Node12Step3Chunk2_2_checked, root5Node12Step3Chunk2_3_checked, root5Node12Step3Chunk2_4_checked, root5Node12Step3Chunk2_5_checked, root5Node12Step3Chunk3_0_checked, root5Node12Step3Chunk3_1_checked, root5Node12Step3Chunk3_2_checked, root5Node12Step3Chunk3_3_checked, root5Node12Step3Chunk3_4_checked, root5Node12Step3Chunk3_5_checked, root5Node12Step3Chunk4_0_checked, root5Node12Step3Chunk4_1_checked, root5Node12Step3Chunk4_2_checked, root5Node12Step3Chunk4_3_checked, root5Node12Step3Chunk4_4_checked, root5Node12Step3Chunk4_5_checked, root5Node12Step3Chunk5_0_checked, root5Node12Step3Chunk5_1_checked, root5Node12Step3Chunk5_2_checked, root5Node12Step3Chunk5_3_checked, root5Node12Step3Chunk5_4_checked, root5Node12Step3Chunk5_5_checked, root5Node12Step3Chunk6_0_checked, root5Node12Step3Chunk6_1_checked, root5Node12Step3Chunk6_2_checked, root5Node12Step3Chunk6_3_checked, root5Node12Step3Chunk6_4_checked, root5Node12Step3Chunk6_5_checked, root5Node12Step3Chunk7_0_checked, root5Node12Step3Chunk7_1_checked, root5Node12Step3Chunk7_2_checked, root5Node12Step3Chunk7_3_checked, root5Node12Step3Chunk7_4_checked, root5Node12Step3Chunk7_5_checked, root5Node12Step3Chunk8_0_checked, root5Node12Step3Chunk8_1_checked, root5Node12Step3Chunk8_2_checked, root5Node12Step3Chunk8_3_checked, root5Node12Step3Chunk8_4_checked, root5Node12Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node12Domains4 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0),(8,0)]
  | 1 => [(4,3),(8,3)]
  | 2 => [(1,5),(3,5),(5,5),(7,5)]
  | 3 => [(0,3),(1,0),(3,0),(6,1)]
  | 4 => [(4,4),(7,2),(8,4)]
  | 5 => [(1,4),(7,4)]
  | 6 => [(0,5),(6,3)]
  | 7 => [(2,0),(2,2),(2,4),(4,4)]
  | 8 => [(0,0),(1,3),(3,3),(7,3)]
  | 9 => [(1,1),(6,1),(7,1)]
  | 10 => [(4,1),(7,5)]
  | 11 => [(0,2),(6,0)]
  | 12 => [(1,1),(3,1),(7,1)]
  | 13 => [(0,1),(1,5),(6,5)]
  | 14 => [(0,4),(6,1),(6,2)]
  | 15 => [(4,0),(7,0),(8,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2),(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(1,0),(7,0)]
  | 21 => [(4,3),(7,1),(8,3)]
  | 22 => [(0,1),(6,4)]
  | 23 => [(1,2),(6,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(0,3),(1,0)]
  | 29 => [(7,1),(8,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(4,1),(5,1),(8,1)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5),(5,5),(8,5)]
  | 35 => [(7,0)]
  | _ => [(7,3),(8,3)]
def root5Node12Domains4Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0),(8,0)]
  | 1 => some [(4,3),(8,3)]
  | 2 => some [(1,5),(3,5),(5,5),(7,5)]
  | 3 => some [(0,3),(1,0),(3,0),(6,1)]
  | 4 => some [(4,4),(7,2),(8,4)]
  | 5 => some [(1,4),(7,4)]
  | 6 => some [(0,5),(6,3)]
  | 7 => some [(2,0),(2,2),(2,4),(4,4)]
  | 8 => some [(0,0),(1,3),(3,3),(7,3)]
  | 9 => some [(1,1),(6,1),(7,1)]
  | 10 => some [(4,1),(7,5)]
  | 11 => some [(0,2),(6,0)]
  | 12 => some [(1,1),(3,1),(7,1)]
  | 13 => some [(0,1),(1,5),(6,5)]
  | 14 => some [(0,4),(6,1),(6,2)]
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2),(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0),(7,0)]
  | 21 => some [(4,3),(7,1),(8,3)]
  | 22 => some [(0,1),(6,4)]
  | 23 => some [(1,2),(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(0,3),(1,0)]
  | 29 => some [(7,1),(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1),(5,1),(8,1)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(5,5),(8,5)]
  | 35 => some [(7,0)]
  | _ => some [(7,3),(8,3)]
theorem root5Node12Domains4_fast_eq : root5Node12Domains4 = expandDomains root5Node12Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node12Domains4 v = expandDomains root5Node12Domains4Fast v from by decide) v
theorem root5Node12Step4Chunk0_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_0⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk0_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_1⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk0_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_2⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk0_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_3⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk0_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_4⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk0_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_5⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk1_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_0⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk1_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_1⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk1_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_2⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk1_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_3⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk1_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_4⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk1_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_5⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk2_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_0⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk2_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_1⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk2_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_2⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk2_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_3⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk2_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_4⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk2_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_5⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk3_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_0⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk3_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_1⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk3_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_2⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk3_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_3⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk3_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_4⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk3_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_5⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk4_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_0⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk4_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_1⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk4_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_2⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk4_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_3⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk4_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_4⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk4_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_5⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk5_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_0⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk5_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_1⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk5_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_2⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk5_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_3⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk5_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_4⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk5_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_5⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk6_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_0⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk6_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_1⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk6_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_2⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk6_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_3⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk6_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_4⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk6_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_5⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk7_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_0⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk7_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_1⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk7_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_2⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk7_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_3⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk7_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_4⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk7_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_5⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk8_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_0⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk8_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_1⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk8_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_2⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk8_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_3⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk8_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_4⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4Chunk8_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_5⟩
      root5Node12Domains3 root5Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node12Domains3 root5Node12Domains4
    root5Node12Domains3Fast root5Node12Domains4Fast
    root5Node12Domains3_fast_eq root5Node12Domains4_fast_eq (by decide)
theorem root5Node12Step4_checked :
    checkReplacement table24 root5Node12Domains3 root5Node12Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node12Step4Chunk0_0_checked, root5Node12Step4Chunk0_1_checked, root5Node12Step4Chunk0_2_checked, root5Node12Step4Chunk0_3_checked, root5Node12Step4Chunk0_4_checked, root5Node12Step4Chunk0_5_checked, root5Node12Step4Chunk1_0_checked, root5Node12Step4Chunk1_1_checked, root5Node12Step4Chunk1_2_checked, root5Node12Step4Chunk1_3_checked, root5Node12Step4Chunk1_4_checked, root5Node12Step4Chunk1_5_checked, root5Node12Step4Chunk2_0_checked, root5Node12Step4Chunk2_1_checked, root5Node12Step4Chunk2_2_checked, root5Node12Step4Chunk2_3_checked, root5Node12Step4Chunk2_4_checked, root5Node12Step4Chunk2_5_checked, root5Node12Step4Chunk3_0_checked, root5Node12Step4Chunk3_1_checked, root5Node12Step4Chunk3_2_checked, root5Node12Step4Chunk3_3_checked, root5Node12Step4Chunk3_4_checked, root5Node12Step4Chunk3_5_checked, root5Node12Step4Chunk4_0_checked, root5Node12Step4Chunk4_1_checked, root5Node12Step4Chunk4_2_checked, root5Node12Step4Chunk4_3_checked, root5Node12Step4Chunk4_4_checked, root5Node12Step4Chunk4_5_checked, root5Node12Step4Chunk5_0_checked, root5Node12Step4Chunk5_1_checked, root5Node12Step4Chunk5_2_checked, root5Node12Step4Chunk5_3_checked, root5Node12Step4Chunk5_4_checked, root5Node12Step4Chunk5_5_checked, root5Node12Step4Chunk6_0_checked, root5Node12Step4Chunk6_1_checked, root5Node12Step4Chunk6_2_checked, root5Node12Step4Chunk6_3_checked, root5Node12Step4Chunk6_4_checked, root5Node12Step4Chunk6_5_checked, root5Node12Step4Chunk7_0_checked, root5Node12Step4Chunk7_1_checked, root5Node12Step4Chunk7_2_checked, root5Node12Step4Chunk7_3_checked, root5Node12Step4Chunk7_4_checked, root5Node12Step4Chunk7_5_checked, root5Node12Step4Chunk8_0_checked, root5Node12Step4Chunk8_1_checked, root5Node12Step4Chunk8_2_checked, root5Node12Step4Chunk8_3_checked, root5Node12Step4Chunk8_4_checked, root5Node12Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node13Domains0 : Domains 37 State := restrict root5Node12Domains4 0 (7,0)
def root5Node13Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3),(8,3)]
  | 2 => some [(1,5),(3,5),(5,5),(7,5)]
  | 3 => some [(0,3),(1,0),(3,0),(6,1)]
  | 4 => some [(4,4),(7,2),(8,4)]
  | 5 => some [(1,4),(7,4)]
  | 6 => some [(0,5),(6,3)]
  | 7 => some [(2,0),(2,2),(2,4),(4,4)]
  | 8 => some [(0,0),(1,3),(3,3),(7,3)]
  | 9 => some [(1,1),(6,1),(7,1)]
  | 10 => some [(4,1),(7,5)]
  | 11 => some [(0,2),(6,0)]
  | 12 => some [(1,1),(3,1),(7,1)]
  | 13 => some [(0,1),(1,5),(6,5)]
  | 14 => some [(0,4),(6,1),(6,2)]
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2),(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0),(7,0)]
  | 21 => some [(4,3),(7,1),(8,3)]
  | 22 => some [(0,1),(6,4)]
  | 23 => some [(1,2),(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(0,3),(1,0)]
  | 29 => some [(7,1),(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1),(5,1),(8,1)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(5,5),(8,5)]
  | 35 => some [(7,0)]
  | _ => some [(7,3),(8,3)]
theorem root5Node13Domains0_fast_eq : root5Node13Domains0 = expandDomains root5Node13Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node13Domains0 v = expandDomains root5Node13Domains0Fast v from by decide) v
def root5Node13Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3),(8,3)]
  | 2 => [(1,5),(3,5),(5,5),(7,5)]
  | 3 => [(0,3),(1,0),(3,0),(6,1)]
  | 4 => [(4,4),(7,2)]
  | 5 => [(1,4),(7,4)]
  | 6 => [(0,5),(6,3)]
  | 7 => [(2,0),(2,2),(2,4),(4,4)]
  | 8 => [(0,0),(1,3),(3,3),(7,3)]
  | 9 => [(1,1),(6,1),(7,1)]
  | 10 => [(4,1),(7,5)]
  | 11 => [(0,2),(6,0)]
  | 12 => [(1,1),(3,1),(7,1)]
  | 13 => [(0,1),(1,5),(6,5)]
  | 14 => [(0,4),(6,1),(6,2)]
  | 15 => [(4,0),(7,0),(8,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2),(8,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(1,0),(7,0)]
  | 21 => [(4,3),(7,1),(8,3)]
  | 22 => [(0,1),(6,4)]
  | 23 => [(1,2),(6,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(0,3),(1,0)]
  | 29 => [(7,1),(8,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(4,1),(5,1),(8,1)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5),(5,5),(8,5)]
  | 35 => [(7,0)]
  | _ => [(7,3),(8,3)]
def root5Node13Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3),(8,3)]
  | 2 => some [(1,5),(3,5),(5,5),(7,5)]
  | 3 => some [(0,3),(1,0),(3,0),(6,1)]
  | 4 => some [(4,4),(7,2)]
  | 5 => some [(1,4),(7,4)]
  | 6 => some [(0,5),(6,3)]
  | 7 => some [(2,0),(2,2),(2,4),(4,4)]
  | 8 => some [(0,0),(1,3),(3,3),(7,3)]
  | 9 => some [(1,1),(6,1),(7,1)]
  | 10 => some [(4,1),(7,5)]
  | 11 => some [(0,2),(6,0)]
  | 12 => some [(1,1),(3,1),(7,1)]
  | 13 => some [(0,1),(1,5),(6,5)]
  | 14 => some [(0,4),(6,1),(6,2)]
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2),(8,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0),(7,0)]
  | 21 => some [(4,3),(7,1),(8,3)]
  | 22 => some [(0,1),(6,4)]
  | 23 => some [(1,2),(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(0,3),(1,0)]
  | 29 => some [(7,1),(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(4,1),(5,1),(8,1)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(5,5),(8,5)]
  | 35 => some [(7,0)]
  | _ => some [(7,3),(8,3)]
theorem root5Node13Domains1_fast_eq : root5Node13Domains1 = expandDomains root5Node13Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node13Domains1 v = expandDomains root5Node13Domains1Fast v from by decide) v
theorem root5Node13Step1Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk4_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk4_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk4_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk4_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk4_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk4_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk5_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk5_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk5_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk5_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk5_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk5_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk6_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk6_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk6_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk6_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk6_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk6_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk7_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk7_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk7_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk7_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk7_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk7_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk8_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_0⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk8_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_1⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk8_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_2⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk8_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_3⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk8_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_4⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1Chunk8_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_5⟩
      root5Node13Domains0 root5Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node13Domains0 root5Node13Domains1
    root5Node13Domains0Fast root5Node13Domains1Fast
    root5Node13Domains0_fast_eq root5Node13Domains1_fast_eq (by decide)
theorem root5Node13Step1_checked :
    checkReplacement table0 root5Node13Domains0 root5Node13Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node13Step1Chunk0_0_checked, root5Node13Step1Chunk0_1_checked, root5Node13Step1Chunk0_2_checked, root5Node13Step1Chunk0_3_checked, root5Node13Step1Chunk0_4_checked, root5Node13Step1Chunk0_5_checked, root5Node13Step1Chunk1_0_checked, root5Node13Step1Chunk1_1_checked, root5Node13Step1Chunk1_2_checked, root5Node13Step1Chunk1_3_checked, root5Node13Step1Chunk1_4_checked, root5Node13Step1Chunk1_5_checked, root5Node13Step1Chunk2_0_checked, root5Node13Step1Chunk2_1_checked, root5Node13Step1Chunk2_2_checked, root5Node13Step1Chunk2_3_checked, root5Node13Step1Chunk2_4_checked, root5Node13Step1Chunk2_5_checked, root5Node13Step1Chunk3_0_checked, root5Node13Step1Chunk3_1_checked, root5Node13Step1Chunk3_2_checked, root5Node13Step1Chunk3_3_checked, root5Node13Step1Chunk3_4_checked, root5Node13Step1Chunk3_5_checked, root5Node13Step1Chunk4_0_checked, root5Node13Step1Chunk4_1_checked, root5Node13Step1Chunk4_2_checked, root5Node13Step1Chunk4_3_checked, root5Node13Step1Chunk4_4_checked, root5Node13Step1Chunk4_5_checked, root5Node13Step1Chunk5_0_checked, root5Node13Step1Chunk5_1_checked, root5Node13Step1Chunk5_2_checked, root5Node13Step1Chunk5_3_checked, root5Node13Step1Chunk5_4_checked, root5Node13Step1Chunk5_5_checked, root5Node13Step1Chunk6_0_checked, root5Node13Step1Chunk6_1_checked, root5Node13Step1Chunk6_2_checked, root5Node13Step1Chunk6_3_checked, root5Node13Step1Chunk6_4_checked, root5Node13Step1Chunk6_5_checked, root5Node13Step1Chunk7_0_checked, root5Node13Step1Chunk7_1_checked, root5Node13Step1Chunk7_2_checked, root5Node13Step1Chunk7_3_checked, root5Node13Step1Chunk7_4_checked, root5Node13Step1Chunk7_5_checked, root5Node13Step1Chunk8_0_checked, root5Node13Step1Chunk8_1_checked, root5Node13Step1Chunk8_2_checked, root5Node13Step1Chunk8_3_checked, root5Node13Step1Chunk8_4_checked, root5Node13Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
