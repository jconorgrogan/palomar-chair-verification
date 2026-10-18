module

public import SpectreFinite.RadiusThreeRoot7Part29
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable1
public import SpectreFinite.RadiusThreeTable19
public import SpectreFinite.RadiusThreeTable24

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node45Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(3,5),(4,2),(7,0)]
  | 1 => [(0,3),(4,3),(5,3),(8,3)]
  | 2 => [(4,1),(7,5),(8,5)]
  | 3 => [(0,2),(0,3),(1,0),(6,0)]
  | 4 => [(0,5)]
  | 5 => [(2,4)]
  | 6 => [(1,3)]
  | 7 => [(5,2),(8,2)]
  | 8 => [(8,0)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(1,4),(6,4)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(0,3),(6,0)]
  | 22 => [(8,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(7,4)]
  | 26 => [(1,3),(6,3)]
  | 27 => [(2,2),(4,2),(7,2),(8,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(4,1),(8,1)]
  | 31 => [(0,2),(6,5)]
  | 32 => [(0,4),(1,1)]
  | 33 => [(2,0),(4,0),(7,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | _ => [(3,0),(5,0),(5,3),(7,0),(8,0)]
def root7Node45Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(3,5),(4,2),(7,0)]
  | 1 => some [(0,3),(4,3),(5,3),(8,3)]
  | 2 => some [(4,1),(7,5),(8,5)]
  | 3 => some [(0,2),(0,3),(1,0),(6,0)]
  | 4 => some [(0,5)]
  | 5 => some [(2,4)]
  | 6 => some [(1,3)]
  | 7 => some [(5,2),(8,2)]
  | 8 => some [(8,0)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(1,4),(6,4)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(8,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(1,3),(6,3)]
  | 27 => some [(2,2),(4,2),(7,2),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(4,1),(8,1)]
  | 31 => some [(0,2),(6,5)]
  | 32 => some [(0,4),(1,1)]
  | 33 => some [(2,0),(4,0),(7,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | _ => some [(3,0),(5,0),(5,3),(7,0),(8,0)]
theorem root7Node45Domains2_fast_eq : root7Node45Domains2 = expandDomains root7Node45Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node45Domains2 v = expandDomains root7Node45Domains2Fast v from by decide) v
theorem root7Node45Step2Chunk0_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_0⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk0_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_1⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk0_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_2⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk0_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_3⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk0_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_4⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk0_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_5⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk1_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_0⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk1_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_1⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk1_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_2⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk1_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_3⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk1_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_4⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk1_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_5⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk2_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_0⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk2_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_1⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk2_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_2⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk2_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_3⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk2_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_4⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk2_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_5⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk3_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_0⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk3_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_1⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk3_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_2⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk3_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_3⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk3_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_4⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk3_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_5⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk4_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_0⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk4_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_1⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk4_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_2⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk4_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_3⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk4_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_4⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk4_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_5⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk5_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_0⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk5_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_1⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk5_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_2⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk5_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_3⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk5_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_4⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk5_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_5⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk6_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_0⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk6_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_1⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk6_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_2⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk6_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_3⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk6_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_4⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk6_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_5⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk7_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_0⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk7_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_1⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk7_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_2⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk7_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_3⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk7_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_4⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk7_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_5⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk8_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_0⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk8_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_1⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk8_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_2⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk8_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_3⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk8_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_4⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2Chunk8_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_5⟩
      root7Node45Domains1 root7Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains1 root7Node45Domains2
    root7Node45Domains1Fast root7Node45Domains2Fast
    root7Node45Domains1_fast_eq root7Node45Domains2_fast_eq (by decide)
theorem root7Node45Step2_checked :
    checkReplacement table19 root7Node45Domains1 root7Node45Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node45Step2Chunk0_0_checked, root7Node45Step2Chunk0_1_checked, root7Node45Step2Chunk0_2_checked, root7Node45Step2Chunk0_3_checked, root7Node45Step2Chunk0_4_checked, root7Node45Step2Chunk0_5_checked, root7Node45Step2Chunk1_0_checked, root7Node45Step2Chunk1_1_checked, root7Node45Step2Chunk1_2_checked, root7Node45Step2Chunk1_3_checked, root7Node45Step2Chunk1_4_checked, root7Node45Step2Chunk1_5_checked, root7Node45Step2Chunk2_0_checked, root7Node45Step2Chunk2_1_checked, root7Node45Step2Chunk2_2_checked, root7Node45Step2Chunk2_3_checked, root7Node45Step2Chunk2_4_checked, root7Node45Step2Chunk2_5_checked, root7Node45Step2Chunk3_0_checked, root7Node45Step2Chunk3_1_checked, root7Node45Step2Chunk3_2_checked, root7Node45Step2Chunk3_3_checked, root7Node45Step2Chunk3_4_checked, root7Node45Step2Chunk3_5_checked, root7Node45Step2Chunk4_0_checked, root7Node45Step2Chunk4_1_checked, root7Node45Step2Chunk4_2_checked, root7Node45Step2Chunk4_3_checked, root7Node45Step2Chunk4_4_checked, root7Node45Step2Chunk4_5_checked, root7Node45Step2Chunk5_0_checked, root7Node45Step2Chunk5_1_checked, root7Node45Step2Chunk5_2_checked, root7Node45Step2Chunk5_3_checked, root7Node45Step2Chunk5_4_checked, root7Node45Step2Chunk5_5_checked, root7Node45Step2Chunk6_0_checked, root7Node45Step2Chunk6_1_checked, root7Node45Step2Chunk6_2_checked, root7Node45Step2Chunk6_3_checked, root7Node45Step2Chunk6_4_checked, root7Node45Step2Chunk6_5_checked, root7Node45Step2Chunk7_0_checked, root7Node45Step2Chunk7_1_checked, root7Node45Step2Chunk7_2_checked, root7Node45Step2Chunk7_3_checked, root7Node45Step2Chunk7_4_checked, root7Node45Step2Chunk7_5_checked, root7Node45Step2Chunk8_0_checked, root7Node45Step2Chunk8_1_checked, root7Node45Step2Chunk8_2_checked, root7Node45Step2Chunk8_3_checked, root7Node45Step2Chunk8_4_checked, root7Node45Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node45Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(3,5)]
  | 1 => [(0,3)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(0,5)]
  | 5 => [(2,4)]
  | 6 => [(1,3)]
  | 7 => [(5,2)]
  | 8 => [(8,0)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(1,4),(6,4)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(0,3),(6,0)]
  | 22 => [(8,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(7,4)]
  | 26 => [(1,3),(6,3)]
  | 27 => [(2,2),(4,2),(7,2),(8,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(4,1),(8,1)]
  | 31 => [(0,2),(6,5)]
  | 32 => [(0,4),(1,1)]
  | 33 => [(2,0),(4,0),(7,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | _ => [(3,0),(5,0),(5,3),(7,0),(8,0)]
def root7Node45Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(3,5)]
  | 1 => some [(0,3)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(0,5)]
  | 5 => some [(2,4)]
  | 6 => some [(1,3)]
  | 7 => some [(5,2)]
  | 8 => some [(8,0)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(1,4),(6,4)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(8,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(1,3),(6,3)]
  | 27 => some [(2,2),(4,2),(7,2),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(4,1),(8,1)]
  | 31 => some [(0,2),(6,5)]
  | 32 => some [(0,4),(1,1)]
  | 33 => some [(2,0),(4,0),(7,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | _ => some [(3,0),(5,0),(5,3),(7,0),(8,0)]
theorem root7Node45Domains3_fast_eq : root7Node45Domains3 = expandDomains root7Node45Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node45Domains3 v = expandDomains root7Node45Domains3Fast v from by decide) v
theorem root7Node45Step3Chunk0_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_0⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk0_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_1⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk0_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_2⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk0_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_3⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk0_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_4⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk0_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_5⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk1_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_0⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk1_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_1⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk1_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_2⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk1_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_3⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk1_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_4⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk1_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_5⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk2_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_0⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk2_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_1⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk2_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_2⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk2_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_3⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk2_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_4⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk2_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_5⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk3_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_0⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk3_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_1⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk3_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_2⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk3_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_3⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk3_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_4⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk3_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_5⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk4_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_0⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk4_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_1⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk4_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_2⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk4_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_3⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk4_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_4⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk4_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_5⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk5_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_0⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk5_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_1⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk5_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_2⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk5_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_3⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk5_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_4⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk5_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_5⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk6_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_0⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk6_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_1⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk6_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_2⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk6_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_3⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk6_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_4⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk6_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_5⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk7_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_0⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk7_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_1⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk7_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_2⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk7_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_3⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk7_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_4⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk7_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_5⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk8_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_0⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk8_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_1⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk8_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_2⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk8_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_3⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk8_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_4⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3Chunk8_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_5⟩
      root7Node45Domains2 root7Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains2 root7Node45Domains3
    root7Node45Domains2Fast root7Node45Domains3Fast
    root7Node45Domains2_fast_eq root7Node45Domains3_fast_eq (by decide)
theorem root7Node45Step3_checked :
    checkReplacement table1 root7Node45Domains2 root7Node45Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node45Step3Chunk0_0_checked, root7Node45Step3Chunk0_1_checked, root7Node45Step3Chunk0_2_checked, root7Node45Step3Chunk0_3_checked, root7Node45Step3Chunk0_4_checked, root7Node45Step3Chunk0_5_checked, root7Node45Step3Chunk1_0_checked, root7Node45Step3Chunk1_1_checked, root7Node45Step3Chunk1_2_checked, root7Node45Step3Chunk1_3_checked, root7Node45Step3Chunk1_4_checked, root7Node45Step3Chunk1_5_checked, root7Node45Step3Chunk2_0_checked, root7Node45Step3Chunk2_1_checked, root7Node45Step3Chunk2_2_checked, root7Node45Step3Chunk2_3_checked, root7Node45Step3Chunk2_4_checked, root7Node45Step3Chunk2_5_checked, root7Node45Step3Chunk3_0_checked, root7Node45Step3Chunk3_1_checked, root7Node45Step3Chunk3_2_checked, root7Node45Step3Chunk3_3_checked, root7Node45Step3Chunk3_4_checked, root7Node45Step3Chunk3_5_checked, root7Node45Step3Chunk4_0_checked, root7Node45Step3Chunk4_1_checked, root7Node45Step3Chunk4_2_checked, root7Node45Step3Chunk4_3_checked, root7Node45Step3Chunk4_4_checked, root7Node45Step3Chunk4_5_checked, root7Node45Step3Chunk5_0_checked, root7Node45Step3Chunk5_1_checked, root7Node45Step3Chunk5_2_checked, root7Node45Step3Chunk5_3_checked, root7Node45Step3Chunk5_4_checked, root7Node45Step3Chunk5_5_checked, root7Node45Step3Chunk6_0_checked, root7Node45Step3Chunk6_1_checked, root7Node45Step3Chunk6_2_checked, root7Node45Step3Chunk6_3_checked, root7Node45Step3Chunk6_4_checked, root7Node45Step3Chunk6_5_checked, root7Node45Step3Chunk7_0_checked, root7Node45Step3Chunk7_1_checked, root7Node45Step3Chunk7_2_checked, root7Node45Step3Chunk7_3_checked, root7Node45Step3Chunk7_4_checked, root7Node45Step3Chunk7_5_checked, root7Node45Step3Chunk8_0_checked, root7Node45Step3Chunk8_1_checked, root7Node45Step3Chunk8_2_checked, root7Node45Step3Chunk8_3_checked, root7Node45Step3Chunk8_4_checked, root7Node45Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node45Domains4 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(3,5)]
  | 1 => [(0,3)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(0,5)]
  | 5 => [(2,4)]
  | 6 => [(1,3)]
  | 7 => [(5,2)]
  | 8 => [(8,0)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(1,4),(6,4)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(0,3),(6,0)]
  | 22 => [(8,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(7,4)]
  | 26 => [(1,3),(6,3)]
  | 27 => [(2,2),(4,2),(7,2),(8,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(4,1),(8,1)]
  | 31 => [(0,2),(6,5)]
  | 32 => [(0,4),(1,1)]
  | 33 => [(7,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(5,2),(5,5),(8,5)]
  | _ => [(3,0),(5,0),(5,3),(7,0),(8,0)]
def root7Node45Domains4Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(3,5)]
  | 1 => some [(0,3)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(0,5)]
  | 5 => some [(2,4)]
  | 6 => some [(1,3)]
  | 7 => some [(5,2)]
  | 8 => some [(8,0)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(1,4),(6,4)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(8,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(1,3),(6,3)]
  | 27 => some [(2,2),(4,2),(7,2),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(4,1),(8,1)]
  | 31 => some [(0,2),(6,5)]
  | 32 => some [(0,4),(1,1)]
  | 33 => some [(7,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5),(8,5)]
  | _ => some [(3,0),(5,0),(5,3),(7,0),(8,0)]
theorem root7Node45Domains4_fast_eq : root7Node45Domains4 = expandDomains root7Node45Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node45Domains4 v = expandDomains root7Node45Domains4Fast v from by decide) v
theorem root7Node45Step4Chunk0_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_0⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk0_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_1⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk0_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_2⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk0_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_3⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk0_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_4⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk0_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_5⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk1_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_0⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk1_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_1⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk1_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_2⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk1_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_3⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk1_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_4⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk1_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_5⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk2_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_0⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk2_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_1⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk2_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_2⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk2_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_3⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk2_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_4⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk2_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_5⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk3_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_0⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk3_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_1⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk3_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_2⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk3_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_3⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk3_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_4⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk3_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_5⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk4_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_0⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk4_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_1⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk4_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_2⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk4_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_3⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk4_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_4⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk4_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_5⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk5_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_0⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk5_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_1⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk5_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_2⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk5_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_3⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk5_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_4⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk5_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_5⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk6_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_0⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk6_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_1⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk6_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_2⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk6_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_3⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk6_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_4⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk6_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_5⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk7_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_0⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk7_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_1⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk7_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_2⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk7_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_3⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk7_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_4⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk7_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_5⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk8_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_0⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk8_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_1⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk8_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_2⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk8_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_3⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk8_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_4⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4Chunk8_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_5⟩
      root7Node45Domains3 root7Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains3 root7Node45Domains4
    root7Node45Domains3Fast root7Node45Domains4Fast
    root7Node45Domains3_fast_eq root7Node45Domains4_fast_eq (by decide)
theorem root7Node45Step4_checked :
    checkReplacement table24 root7Node45Domains3 root7Node45Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node45Step4Chunk0_0_checked, root7Node45Step4Chunk0_1_checked, root7Node45Step4Chunk0_2_checked, root7Node45Step4Chunk0_3_checked, root7Node45Step4Chunk0_4_checked, root7Node45Step4Chunk0_5_checked, root7Node45Step4Chunk1_0_checked, root7Node45Step4Chunk1_1_checked, root7Node45Step4Chunk1_2_checked, root7Node45Step4Chunk1_3_checked, root7Node45Step4Chunk1_4_checked, root7Node45Step4Chunk1_5_checked, root7Node45Step4Chunk2_0_checked, root7Node45Step4Chunk2_1_checked, root7Node45Step4Chunk2_2_checked, root7Node45Step4Chunk2_3_checked, root7Node45Step4Chunk2_4_checked, root7Node45Step4Chunk2_5_checked, root7Node45Step4Chunk3_0_checked, root7Node45Step4Chunk3_1_checked, root7Node45Step4Chunk3_2_checked, root7Node45Step4Chunk3_3_checked, root7Node45Step4Chunk3_4_checked, root7Node45Step4Chunk3_5_checked, root7Node45Step4Chunk4_0_checked, root7Node45Step4Chunk4_1_checked, root7Node45Step4Chunk4_2_checked, root7Node45Step4Chunk4_3_checked, root7Node45Step4Chunk4_4_checked, root7Node45Step4Chunk4_5_checked, root7Node45Step4Chunk5_0_checked, root7Node45Step4Chunk5_1_checked, root7Node45Step4Chunk5_2_checked, root7Node45Step4Chunk5_3_checked, root7Node45Step4Chunk5_4_checked, root7Node45Step4Chunk5_5_checked, root7Node45Step4Chunk6_0_checked, root7Node45Step4Chunk6_1_checked, root7Node45Step4Chunk6_2_checked, root7Node45Step4Chunk6_3_checked, root7Node45Step4Chunk6_4_checked, root7Node45Step4Chunk6_5_checked, root7Node45Step4Chunk7_0_checked, root7Node45Step4Chunk7_1_checked, root7Node45Step4Chunk7_2_checked, root7Node45Step4Chunk7_3_checked, root7Node45Step4Chunk7_4_checked, root7Node45Step4Chunk7_5_checked, root7Node45Step4Chunk8_0_checked, root7Node45Step4Chunk8_1_checked, root7Node45Step4Chunk8_2_checked, root7Node45Step4Chunk8_3_checked, root7Node45Step4Chunk8_4_checked, root7Node45Step4Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
