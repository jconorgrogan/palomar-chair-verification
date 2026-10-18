module

public import SpectreFinite.RadiusFourRoot1Part15
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable26
public import SpectreFinite.RadiusFourTable29
public import SpectreFinite.RadiusFourTable35
public import SpectreFinite.RadiusFourTable4
public import SpectreFinite.RadiusFourTable40

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node45Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,5)]
  | 6 => [(1,0)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5),(7,3)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(0,0)]
  | 25 => [(1,2),(7,2)]
  | 26 => [(8,5)]
  | 27 => [(7,0)]
  | 28 => [(8,3)]
  | 29 => [(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5)]
  | 33 => [(6,1)]
  | 34 => [(8,1)]
  | 35 => [(7,2)]
  | 36 => [(7,4)]
  | 37 => [(1,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(7,0)]
  | 42 => [(8,3)]
  | 43 => [(8,1)]
  | 44 => [(6,5)]
  | 45 => [(0,4)]
  | 46 => [(5,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(7,4)]
  | 50 => [(5,5)]
  | 51 => [(7,0)]
  | 52 => [(4,3)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(4,1)]
  | 56 => [(4,4),(8,4)]
  | 57 => [(1,4)]
  | 58 => [(0,5)]
  | 59 => [(2,0)]
  | _ => [(7,3)]
def root1Node45Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,5)]
  | 6 => some [(1,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5),(7,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(8,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(8,1)]
  | 35 => some [(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(8,1)]
  | 44 => some [(6,5)]
  | 45 => some [(0,4)]
  | 46 => some [(5,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,5)]
  | 51 => some [(7,0)]
  | 52 => some [(4,3)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(4,1)]
  | 56 => some [(4,4),(8,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(2,0)]
  | _ => some [(7,3)]
theorem root1Node45Domains2_fast_eq : root1Node45Domains2 = expandDomains root1Node45Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node45Domains2 v = expandDomains root1Node45Domains2Fast v from by decide) v
theorem root1Node45Step2Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root1Node45Domains1 root1Node45Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains1 root1Node45Domains2
    root1Node45Domains1Fast root1Node45Domains2Fast
    root1Node45Domains1_fast_eq root1Node45Domains2_fast_eq (by decide)
theorem root1Node45Step2_checked :
    checkReplacement table26 root1Node45Domains1 root1Node45Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node45Step2Chunk0_0_checked, root1Node45Step2Chunk0_1_checked, root1Node45Step2Chunk0_2_checked, root1Node45Step2Chunk0_3_checked, root1Node45Step2Chunk0_4_checked, root1Node45Step2Chunk0_5_checked, root1Node45Step2Chunk1_0_checked, root1Node45Step2Chunk1_1_checked, root1Node45Step2Chunk1_2_checked, root1Node45Step2Chunk1_3_checked, root1Node45Step2Chunk1_4_checked, root1Node45Step2Chunk1_5_checked, root1Node45Step2Chunk2_0_checked, root1Node45Step2Chunk2_1_checked, root1Node45Step2Chunk2_2_checked, root1Node45Step2Chunk2_3_checked, root1Node45Step2Chunk2_4_checked, root1Node45Step2Chunk2_5_checked, root1Node45Step2Chunk3_0_checked, root1Node45Step2Chunk3_1_checked, root1Node45Step2Chunk3_2_checked, root1Node45Step2Chunk3_3_checked, root1Node45Step2Chunk3_4_checked, root1Node45Step2Chunk3_5_checked, root1Node45Step2Chunk4_0_checked, root1Node45Step2Chunk4_1_checked, root1Node45Step2Chunk4_2_checked, root1Node45Step2Chunk4_3_checked, root1Node45Step2Chunk4_4_checked, root1Node45Step2Chunk4_5_checked, root1Node45Step2Chunk5_0_checked, root1Node45Step2Chunk5_1_checked, root1Node45Step2Chunk5_2_checked, root1Node45Step2Chunk5_3_checked, root1Node45Step2Chunk5_4_checked, root1Node45Step2Chunk5_5_checked, root1Node45Step2Chunk6_0_checked, root1Node45Step2Chunk6_1_checked, root1Node45Step2Chunk6_2_checked, root1Node45Step2Chunk6_3_checked, root1Node45Step2Chunk6_4_checked, root1Node45Step2Chunk6_5_checked, root1Node45Step2Chunk7_0_checked, root1Node45Step2Chunk7_1_checked, root1Node45Step2Chunk7_2_checked, root1Node45Step2Chunk7_3_checked, root1Node45Step2Chunk7_4_checked, root1Node45Step2Chunk7_5_checked, root1Node45Step2Chunk8_0_checked, root1Node45Step2Chunk8_1_checked, root1Node45Step2Chunk8_2_checked, root1Node45Step2Chunk8_3_checked, root1Node45Step2Chunk8_4_checked, root1Node45Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node45Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,5)]
  | 6 => [(1,0)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(0,0)]
  | 25 => [(7,2)]
  | 26 => [(8,5)]
  | 27 => [(7,0)]
  | 28 => [(8,3)]
  | 29 => [(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5)]
  | 33 => [(6,1)]
  | 34 => [(8,1)]
  | 35 => [(7,2)]
  | 36 => [(7,4)]
  | 37 => [(1,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(7,0)]
  | 42 => [(8,3)]
  | 43 => [(8,1)]
  | 44 => [(6,5)]
  | 45 => [(0,4)]
  | 46 => [(5,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(7,4)]
  | 50 => [(5,5)]
  | 51 => [(7,0)]
  | 52 => [(4,3)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(4,1)]
  | 56 => [(4,4),(8,4)]
  | 57 => [(1,4)]
  | 58 => [(0,5)]
  | 59 => [(2,0)]
  | _ => [(7,3)]
def root1Node45Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,5)]
  | 6 => some [(1,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0)]
  | 25 => some [(7,2)]
  | 26 => some [(8,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(8,1)]
  | 35 => some [(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(8,1)]
  | 44 => some [(6,5)]
  | 45 => some [(0,4)]
  | 46 => some [(5,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,5)]
  | 51 => some [(7,0)]
  | 52 => some [(4,3)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(4,1)]
  | 56 => some [(4,4),(8,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(2,0)]
  | _ => some [(7,3)]
theorem root1Node45Domains3_fast_eq : root1Node45Domains3 = expandDomains root1Node45Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node45Domains3 v = expandDomains root1Node45Domains3Fast v from by decide) v
theorem root1Node45Step3Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root1Node45Domains2 root1Node45Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains2 root1Node45Domains3
    root1Node45Domains2Fast root1Node45Domains3Fast
    root1Node45Domains2_fast_eq root1Node45Domains3_fast_eq (by decide)
theorem root1Node45Step3_checked :
    checkReplacement table4 root1Node45Domains2 root1Node45Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node45Step3Chunk0_0_checked, root1Node45Step3Chunk0_1_checked, root1Node45Step3Chunk0_2_checked, root1Node45Step3Chunk0_3_checked, root1Node45Step3Chunk0_4_checked, root1Node45Step3Chunk0_5_checked, root1Node45Step3Chunk1_0_checked, root1Node45Step3Chunk1_1_checked, root1Node45Step3Chunk1_2_checked, root1Node45Step3Chunk1_3_checked, root1Node45Step3Chunk1_4_checked, root1Node45Step3Chunk1_5_checked, root1Node45Step3Chunk2_0_checked, root1Node45Step3Chunk2_1_checked, root1Node45Step3Chunk2_2_checked, root1Node45Step3Chunk2_3_checked, root1Node45Step3Chunk2_4_checked, root1Node45Step3Chunk2_5_checked, root1Node45Step3Chunk3_0_checked, root1Node45Step3Chunk3_1_checked, root1Node45Step3Chunk3_2_checked, root1Node45Step3Chunk3_3_checked, root1Node45Step3Chunk3_4_checked, root1Node45Step3Chunk3_5_checked, root1Node45Step3Chunk4_0_checked, root1Node45Step3Chunk4_1_checked, root1Node45Step3Chunk4_2_checked, root1Node45Step3Chunk4_3_checked, root1Node45Step3Chunk4_4_checked, root1Node45Step3Chunk4_5_checked, root1Node45Step3Chunk5_0_checked, root1Node45Step3Chunk5_1_checked, root1Node45Step3Chunk5_2_checked, root1Node45Step3Chunk5_3_checked, root1Node45Step3Chunk5_4_checked, root1Node45Step3Chunk5_5_checked, root1Node45Step3Chunk6_0_checked, root1Node45Step3Chunk6_1_checked, root1Node45Step3Chunk6_2_checked, root1Node45Step3Chunk6_3_checked, root1Node45Step3Chunk6_4_checked, root1Node45Step3Chunk6_5_checked, root1Node45Step3Chunk7_0_checked, root1Node45Step3Chunk7_1_checked, root1Node45Step3Chunk7_2_checked, root1Node45Step3Chunk7_3_checked, root1Node45Step3Chunk7_4_checked, root1Node45Step3Chunk7_5_checked, root1Node45Step3Chunk8_0_checked, root1Node45Step3Chunk8_1_checked, root1Node45Step3Chunk8_2_checked, root1Node45Step3Chunk8_3_checked, root1Node45Step3Chunk8_4_checked, root1Node45Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node45Domains4 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,5)]
  | 6 => [(1,0)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(0,0)]
  | 25 => [(7,2)]
  | 26 => [(8,5)]
  | 27 => [(7,0)]
  | 28 => [(8,3)]
  | 29 => [(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5)]
  | 33 => [(6,1)]
  | 34 => [(8,1)]
  | 35 => [(7,2)]
  | 36 => [(7,4)]
  | 37 => [(1,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(7,0)]
  | 42 => [(8,3)]
  | 43 => [(8,1)]
  | 44 => [(6,5)]
  | 45 => [(0,4)]
  | 46 => [(5,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(7,4)]
  | 50 => [(5,5)]
  | 51 => [(7,0)]
  | 52 => [(4,3)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(4,1)]
  | 56 => [(4,4)]
  | 57 => [(1,4)]
  | 58 => [(0,5)]
  | 59 => [(2,0)]
  | _ => [(7,3)]
def root1Node45Domains4Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,5)]
  | 6 => some [(1,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0)]
  | 25 => some [(7,2)]
  | 26 => some [(8,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(8,1)]
  | 35 => some [(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(8,1)]
  | 44 => some [(6,5)]
  | 45 => some [(0,4)]
  | 46 => some [(5,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,5)]
  | 51 => some [(7,0)]
  | 52 => some [(4,3)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(4,1)]
  | 56 => some [(4,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(2,0)]
  | _ => some [(7,3)]
theorem root1Node45Domains4_fast_eq : root1Node45Domains4 = expandDomains root1Node45Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node45Domains4 v = expandDomains root1Node45Domains4Fast v from by decide) v
theorem root1Node45Step4Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root1Node45Domains3 root1Node45Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node45Domains3 root1Node45Domains4
    root1Node45Domains3Fast root1Node45Domains4Fast
    root1Node45Domains3_fast_eq root1Node45Domains4_fast_eq (by decide)
theorem root1Node45Step4_checked :
    checkReplacement table35 root1Node45Domains3 root1Node45Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node45Step4Chunk0_0_checked, root1Node45Step4Chunk0_1_checked, root1Node45Step4Chunk0_2_checked, root1Node45Step4Chunk0_3_checked, root1Node45Step4Chunk0_4_checked, root1Node45Step4Chunk0_5_checked, root1Node45Step4Chunk1_0_checked, root1Node45Step4Chunk1_1_checked, root1Node45Step4Chunk1_2_checked, root1Node45Step4Chunk1_3_checked, root1Node45Step4Chunk1_4_checked, root1Node45Step4Chunk1_5_checked, root1Node45Step4Chunk2_0_checked, root1Node45Step4Chunk2_1_checked, root1Node45Step4Chunk2_2_checked, root1Node45Step4Chunk2_3_checked, root1Node45Step4Chunk2_4_checked, root1Node45Step4Chunk2_5_checked, root1Node45Step4Chunk3_0_checked, root1Node45Step4Chunk3_1_checked, root1Node45Step4Chunk3_2_checked, root1Node45Step4Chunk3_3_checked, root1Node45Step4Chunk3_4_checked, root1Node45Step4Chunk3_5_checked, root1Node45Step4Chunk4_0_checked, root1Node45Step4Chunk4_1_checked, root1Node45Step4Chunk4_2_checked, root1Node45Step4Chunk4_3_checked, root1Node45Step4Chunk4_4_checked, root1Node45Step4Chunk4_5_checked, root1Node45Step4Chunk5_0_checked, root1Node45Step4Chunk5_1_checked, root1Node45Step4Chunk5_2_checked, root1Node45Step4Chunk5_3_checked, root1Node45Step4Chunk5_4_checked, root1Node45Step4Chunk5_5_checked, root1Node45Step4Chunk6_0_checked, root1Node45Step4Chunk6_1_checked, root1Node45Step4Chunk6_2_checked, root1Node45Step4Chunk6_3_checked, root1Node45Step4Chunk6_4_checked, root1Node45Step4Chunk6_5_checked, root1Node45Step4Chunk7_0_checked, root1Node45Step4Chunk7_1_checked, root1Node45Step4Chunk7_2_checked, root1Node45Step4Chunk7_3_checked, root1Node45Step4Chunk7_4_checked, root1Node45Step4Chunk7_5_checked, root1Node45Step4Chunk8_0_checked, root1Node45Step4Chunk8_1_checked, root1Node45Step4Chunk8_2_checked, root1Node45Step4Chunk8_3_checked, root1Node45Step4Chunk8_4_checked, root1Node45Step4Chunk8_5_checked, Bool.true_and]
  · decide
theorem root1Node45Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node45Domains4 (.output 21) = true := by decide
def root1Node46Domains0 : Domains 61 State := restrict root1Node44Domains5 16 (8,0)
def root1Node46Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,5)]
  | 6 => some [(1,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(4,5),(7,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0),(6,4)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(4,5),(8,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,1)]
  | 34 => some [(8,1)]
  | 35 => some [(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3),(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0)]
  | 42 => some [(5,3),(8,3)]
  | 43 => some [(4,1),(8,1)]
  | 44 => some [(0,2),(6,5)]
  | 45 => some [(0,4),(1,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,0),(0,1),(6,4)]
  | 48 => some [(1,2),(6,2),(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,2),(5,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(1,5),(3,5),(5,5)]
  | 54 => some [(0,3),(1,0),(6,1)]
  | 55 => some [(2,1),(4,1)]
  | 56 => some [(4,4),(8,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(2,0),(2,4),(4,4)]
  | _ => some [(0,0),(1,3),(7,3)]
theorem root1Node46Domains0_fast_eq : root1Node46Domains0 = expandDomains root1Node46Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node46Domains0 v = expandDomains root1Node46Domains0Fast v from by decide) v
def root1Node46Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,5)]
  | 6 => [(1,0)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(8,2)]
  | 16 => [(8,0)]
  | 17 => [(7,3)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(4,5),(8,5)]
  | 27 => [(7,0)]
  | 28 => [(8,3)]
  | 29 => [(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(0,3)]
  | 34 => [(8,1)]
  | 35 => [(7,2)]
  | 36 => [(7,4)]
  | 37 => [(1,3),(6,3)]
  | 38 => [(7,2),(8,2)]
  | 39 => [(4,0),(8,0)]
  | 40 => [(7,3)]
  | 41 => [(4,2)]
  | 42 => [(5,3)]
  | 43 => [(4,1),(8,1)]
  | 44 => [(0,2),(6,5)]
  | 45 => [(0,4),(1,1)]
  | 46 => [(5,1),(5,4)]
  | 47 => [(0,1),(6,4)]
  | 48 => [(1,2),(6,2)]
  | 49 => [(7,4)]
  | 50 => [(5,2),(5,5)]
  | 51 => [(7,0),(8,0)]
  | 52 => [(4,3),(8,3)]
  | 53 => [(3,5),(5,5)]
  | 54 => [(0,3),(1,0)]
  | 55 => [(2,1),(4,1)]
  | 56 => [(4,4),(8,4)]
  | 57 => [(1,4)]
  | 58 => [(0,5)]
  | 59 => [(2,4),(4,4)]
  | _ => [(0,0),(1,3)]
def root1Node46Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,5)]
  | 6 => some [(1,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(4,5),(8,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(8,1)]
  | 35 => some [(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3),(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(4,1),(8,1)]
  | 44 => some [(0,2),(6,5)]
  | 45 => some [(0,4),(1,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,1),(6,4)]
  | 48 => some [(1,2),(6,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,2),(5,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(3,5),(5,5)]
  | 54 => some [(0,3),(1,0)]
  | 55 => some [(2,1),(4,1)]
  | 56 => some [(4,4),(8,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(2,4),(4,4)]
  | _ => some [(0,0),(1,3)]
theorem root1Node46Domains1_fast_eq : root1Node46Domains1 = expandDomains root1Node46Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node46Domains1 v = expandDomains root1Node46Domains1Fast v from by decide) v
theorem root1Node46Step1Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root1Node46Domains0 root1Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node46Domains0 root1Node46Domains1
    root1Node46Domains0Fast root1Node46Domains1Fast
    root1Node46Domains0_fast_eq root1Node46Domains1_fast_eq (by decide)
theorem root1Node46Step1_checked :
    checkReplacement table40 root1Node46Domains0 root1Node46Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node46Step1Chunk0_0_checked, root1Node46Step1Chunk0_1_checked, root1Node46Step1Chunk0_2_checked, root1Node46Step1Chunk0_3_checked, root1Node46Step1Chunk0_4_checked, root1Node46Step1Chunk0_5_checked, root1Node46Step1Chunk1_0_checked, root1Node46Step1Chunk1_1_checked, root1Node46Step1Chunk1_2_checked, root1Node46Step1Chunk1_3_checked, root1Node46Step1Chunk1_4_checked, root1Node46Step1Chunk1_5_checked, root1Node46Step1Chunk2_0_checked, root1Node46Step1Chunk2_1_checked, root1Node46Step1Chunk2_2_checked, root1Node46Step1Chunk2_3_checked, root1Node46Step1Chunk2_4_checked, root1Node46Step1Chunk2_5_checked, root1Node46Step1Chunk3_0_checked, root1Node46Step1Chunk3_1_checked, root1Node46Step1Chunk3_2_checked, root1Node46Step1Chunk3_3_checked, root1Node46Step1Chunk3_4_checked, root1Node46Step1Chunk3_5_checked, root1Node46Step1Chunk4_0_checked, root1Node46Step1Chunk4_1_checked, root1Node46Step1Chunk4_2_checked, root1Node46Step1Chunk4_3_checked, root1Node46Step1Chunk4_4_checked, root1Node46Step1Chunk4_5_checked, root1Node46Step1Chunk5_0_checked, root1Node46Step1Chunk5_1_checked, root1Node46Step1Chunk5_2_checked, root1Node46Step1Chunk5_3_checked, root1Node46Step1Chunk5_4_checked, root1Node46Step1Chunk5_5_checked, root1Node46Step1Chunk6_0_checked, root1Node46Step1Chunk6_1_checked, root1Node46Step1Chunk6_2_checked, root1Node46Step1Chunk6_3_checked, root1Node46Step1Chunk6_4_checked, root1Node46Step1Chunk6_5_checked, root1Node46Step1Chunk7_0_checked, root1Node46Step1Chunk7_1_checked, root1Node46Step1Chunk7_2_checked, root1Node46Step1Chunk7_3_checked, root1Node46Step1Chunk7_4_checked, root1Node46Step1Chunk7_5_checked, root1Node46Step1Chunk8_0_checked, root1Node46Step1Chunk8_1_checked, root1Node46Step1Chunk8_2_checked, root1Node46Step1Chunk8_3_checked, root1Node46Step1Chunk8_4_checked, root1Node46Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node47Domains0 : Domains 61 State := restrict root1Node46Domains1 26 (4,5)
def root1Node47Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,5)]
  | 6 => some [(1,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(4,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(8,1)]
  | 35 => some [(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3),(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(4,1),(8,1)]
  | 44 => some [(0,2),(6,5)]
  | 45 => some [(0,4),(1,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,1),(6,4)]
  | 48 => some [(1,2),(6,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,2),(5,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(3,5),(5,5)]
  | 54 => some [(0,3),(1,0)]
  | 55 => some [(2,1),(4,1)]
  | 56 => some [(4,4),(8,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(2,4),(4,4)]
  | _ => some [(0,0),(1,3)]
theorem root1Node47Domains0_fast_eq : root1Node47Domains0 = expandDomains root1Node47Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node47Domains0 v = expandDomains root1Node47Domains0Fast v from by decide) v
def root1Node47Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,5)]
  | 6 => [(1,0)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(8,2)]
  | 16 => [(8,0)]
  | 17 => [(7,3)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(4,5)]
  | 27 => [(7,0)]
  | 28 => [(8,3)]
  | 29 => [(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(0,3)]
  | 34 => [(8,1)]
  | 35 => [(7,2)]
  | 36 => [(7,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(4,2)]
  | 42 => [(5,3)]
  | 43 => [(4,1)]
  | 44 => [(0,2)]
  | 45 => [(1,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(1,2),(6,2)]
  | 49 => [(7,4)]
  | 50 => [(5,2)]
  | 51 => [(8,0)]
  | 52 => [(8,3)]
  | 53 => [(5,5)]
  | 54 => [(0,3),(1,0)]
  | 55 => [(2,1),(4,1)]
  | 56 => [(4,4),(8,4)]
  | 57 => [(1,4)]
  | 58 => [(0,5)]
  | 59 => [(2,4),(4,4)]
  | _ => [(0,0),(1,3)]
def root1Node47Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,5)]
  | 6 => some [(1,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(4,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(8,1)]
  | 35 => some [(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(4,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(1,2),(6,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,2)]
  | 51 => some [(8,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5)]
  | 54 => some [(0,3),(1,0)]
  | 55 => some [(2,1),(4,1)]
  | 56 => some [(4,4),(8,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(2,4),(4,4)]
  | _ => some [(0,0),(1,3)]
theorem root1Node47Domains1_fast_eq : root1Node47Domains1 = expandDomains root1Node47Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node47Domains1 v = expandDomains root1Node47Domains1Fast v from by decide) v
theorem root1Node47Step1Chunk0_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_0⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk0_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_1⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk0_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_2⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk0_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_3⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk0_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_4⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk0_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_5⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk1_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_0⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk1_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_1⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk1_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_2⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk1_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_3⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk1_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_4⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk1_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_5⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk2_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_0⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk2_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_1⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk2_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_2⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk2_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_3⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk2_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_4⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk2_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_5⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk3_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_0⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk3_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_1⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk3_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_2⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk3_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_3⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk3_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_4⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk3_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_5⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk4_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_0⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk4_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_1⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk4_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_2⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk4_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_3⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk4_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_4⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk4_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_5⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk5_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_0⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk5_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_1⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk5_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_2⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk5_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_3⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk5_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_4⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk5_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_5⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk6_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_0⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk6_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_1⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk6_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_2⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk6_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_3⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk6_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_4⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk6_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_5⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk7_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_0⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk7_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_1⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk7_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_2⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk7_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_3⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk7_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_4⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk7_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_5⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk8_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_0⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk8_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_1⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk8_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_2⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk8_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_3⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk8_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_4⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1Chunk8_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_5⟩
      root1Node47Domains0 root1Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains0 root1Node47Domains1
    root1Node47Domains0Fast root1Node47Domains1Fast
    root1Node47Domains0_fast_eq root1Node47Domains1_fast_eq (by decide)
theorem root1Node47Step1_checked :
    checkReplacement table29 root1Node47Domains0 root1Node47Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node47Step1Chunk0_0_checked, root1Node47Step1Chunk0_1_checked, root1Node47Step1Chunk0_2_checked, root1Node47Step1Chunk0_3_checked, root1Node47Step1Chunk0_4_checked, root1Node47Step1Chunk0_5_checked, root1Node47Step1Chunk1_0_checked, root1Node47Step1Chunk1_1_checked, root1Node47Step1Chunk1_2_checked, root1Node47Step1Chunk1_3_checked, root1Node47Step1Chunk1_4_checked, root1Node47Step1Chunk1_5_checked, root1Node47Step1Chunk2_0_checked, root1Node47Step1Chunk2_1_checked, root1Node47Step1Chunk2_2_checked, root1Node47Step1Chunk2_3_checked, root1Node47Step1Chunk2_4_checked, root1Node47Step1Chunk2_5_checked, root1Node47Step1Chunk3_0_checked, root1Node47Step1Chunk3_1_checked, root1Node47Step1Chunk3_2_checked, root1Node47Step1Chunk3_3_checked, root1Node47Step1Chunk3_4_checked, root1Node47Step1Chunk3_5_checked, root1Node47Step1Chunk4_0_checked, root1Node47Step1Chunk4_1_checked, root1Node47Step1Chunk4_2_checked, root1Node47Step1Chunk4_3_checked, root1Node47Step1Chunk4_4_checked, root1Node47Step1Chunk4_5_checked, root1Node47Step1Chunk5_0_checked, root1Node47Step1Chunk5_1_checked, root1Node47Step1Chunk5_2_checked, root1Node47Step1Chunk5_3_checked, root1Node47Step1Chunk5_4_checked, root1Node47Step1Chunk5_5_checked, root1Node47Step1Chunk6_0_checked, root1Node47Step1Chunk6_1_checked, root1Node47Step1Chunk6_2_checked, root1Node47Step1Chunk6_3_checked, root1Node47Step1Chunk6_4_checked, root1Node47Step1Chunk6_5_checked, root1Node47Step1Chunk7_0_checked, root1Node47Step1Chunk7_1_checked, root1Node47Step1Chunk7_2_checked, root1Node47Step1Chunk7_3_checked, root1Node47Step1Chunk7_4_checked, root1Node47Step1Chunk7_5_checked, root1Node47Step1Chunk8_0_checked, root1Node47Step1Chunk8_1_checked, root1Node47Step1Chunk8_2_checked, root1Node47Step1Chunk8_3_checked, root1Node47Step1Chunk8_4_checked, root1Node47Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
