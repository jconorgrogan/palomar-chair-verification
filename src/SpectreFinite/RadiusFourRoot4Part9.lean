module

public import SpectreFinite.RadiusFourRoot4Part8
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable16
public import SpectreFinite.RadiusFourTable21
public import SpectreFinite.RadiusFourTable26
public import SpectreFinite.RadiusFourTable4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node25Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(7,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(5,5)]
  | 19 => [(1,0)]
  | 20 => [(2,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(0,0)]
  | 29 => [(3,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(5,0)]
  | 34 => [(4,5)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(0,0)]
  | 43 => [(4,5),(7,3)]
  | 44 => [(7,0)]
  | 45 => [(8,3)]
  | 46 => [(8,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(1,5)]
  | 50 => [(1,2),(7,2)]
  | 51 => [(7,4)]
  | 52 => [(1,3)]
  | 53 => [(8,2)]
  | 54 => [(5,0)]
  | 55 => [(4,5)]
  | 56 => [(8,1)]
  | 57 => [(6,5)]
  | 58 => [(0,4)]
  | 59 => [(5,4)]
  | _ => [(0,0)]
def root4Node25Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(1,0)]
  | 20 => some [(2,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(0,0)]
  | 29 => some [(3,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0)]
  | 43 => some [(4,5),(7,3)]
  | 44 => some [(7,0)]
  | 45 => some [(8,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(1,5)]
  | 50 => some [(1,2),(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3)]
  | 53 => some [(8,2)]
  | 54 => some [(5,0)]
  | 55 => some [(4,5)]
  | 56 => some [(8,1)]
  | 57 => some [(6,5)]
  | 58 => some [(0,4)]
  | 59 => some [(5,4)]
  | _ => some [(0,0)]
theorem root4Node25Domains2_fast_eq : root4Node25Domains2 = expandDomains root4Node25Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node25Domains2 v = expandDomains root4Node25Domains2Fast v from by decide) v
theorem root4Node25Step2Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root4Node25Domains1 root4Node25Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains1 root4Node25Domains2
    root4Node25Domains1Fast root4Node25Domains2Fast
    root4Node25Domains1_fast_eq root4Node25Domains2_fast_eq (by decide)
theorem root4Node25Step2_checked :
    checkReplacement table4 root4Node25Domains1 root4Node25Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node25Step2Chunk0_0_checked, root4Node25Step2Chunk0_1_checked, root4Node25Step2Chunk0_2_checked, root4Node25Step2Chunk0_3_checked, root4Node25Step2Chunk0_4_checked, root4Node25Step2Chunk0_5_checked, root4Node25Step2Chunk1_0_checked, root4Node25Step2Chunk1_1_checked, root4Node25Step2Chunk1_2_checked, root4Node25Step2Chunk1_3_checked, root4Node25Step2Chunk1_4_checked, root4Node25Step2Chunk1_5_checked, root4Node25Step2Chunk2_0_checked, root4Node25Step2Chunk2_1_checked, root4Node25Step2Chunk2_2_checked, root4Node25Step2Chunk2_3_checked, root4Node25Step2Chunk2_4_checked, root4Node25Step2Chunk2_5_checked, root4Node25Step2Chunk3_0_checked, root4Node25Step2Chunk3_1_checked, root4Node25Step2Chunk3_2_checked, root4Node25Step2Chunk3_3_checked, root4Node25Step2Chunk3_4_checked, root4Node25Step2Chunk3_5_checked, root4Node25Step2Chunk4_0_checked, root4Node25Step2Chunk4_1_checked, root4Node25Step2Chunk4_2_checked, root4Node25Step2Chunk4_3_checked, root4Node25Step2Chunk4_4_checked, root4Node25Step2Chunk4_5_checked, root4Node25Step2Chunk5_0_checked, root4Node25Step2Chunk5_1_checked, root4Node25Step2Chunk5_2_checked, root4Node25Step2Chunk5_3_checked, root4Node25Step2Chunk5_4_checked, root4Node25Step2Chunk5_5_checked, root4Node25Step2Chunk6_0_checked, root4Node25Step2Chunk6_1_checked, root4Node25Step2Chunk6_2_checked, root4Node25Step2Chunk6_3_checked, root4Node25Step2Chunk6_4_checked, root4Node25Step2Chunk6_5_checked, root4Node25Step2Chunk7_0_checked, root4Node25Step2Chunk7_1_checked, root4Node25Step2Chunk7_2_checked, root4Node25Step2Chunk7_3_checked, root4Node25Step2Chunk7_4_checked, root4Node25Step2Chunk7_5_checked, root4Node25Step2Chunk8_0_checked, root4Node25Step2Chunk8_1_checked, root4Node25Step2Chunk8_2_checked, root4Node25Step2Chunk8_3_checked, root4Node25Step2Chunk8_4_checked, root4Node25Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node25Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(7,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(5,5)]
  | 19 => [(1,0)]
  | 20 => [(2,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(0,0)]
  | 29 => [(3,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(5,0)]
  | 34 => [(4,5)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(0,0)]
  | 43 => [(4,5)]
  | 44 => [(7,0)]
  | 45 => [(8,3)]
  | 46 => [(8,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(1,5)]
  | 50 => [(7,2)]
  | 51 => [(7,4)]
  | 52 => [(1,3)]
  | 53 => [(8,2)]
  | 54 => [(5,0)]
  | 55 => [(4,5)]
  | 56 => [(8,1)]
  | 57 => [(6,5)]
  | 58 => [(0,4)]
  | 59 => [(5,4)]
  | _ => [(0,0)]
def root4Node25Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(1,0)]
  | 20 => some [(2,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(0,0)]
  | 29 => some [(3,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0)]
  | 43 => some [(4,5)]
  | 44 => some [(7,0)]
  | 45 => some [(8,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(1,5)]
  | 50 => some [(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3)]
  | 53 => some [(8,2)]
  | 54 => some [(5,0)]
  | 55 => some [(4,5)]
  | 56 => some [(8,1)]
  | 57 => some [(6,5)]
  | 58 => some [(0,4)]
  | 59 => some [(5,4)]
  | _ => some [(0,0)]
theorem root4Node25Domains3_fast_eq : root4Node25Domains3 = expandDomains root4Node25Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node25Domains3 v = expandDomains root4Node25Domains3Fast v from by decide) v
theorem root4Node25Step3Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root4Node25Domains2 root4Node25Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains2 root4Node25Domains3
    root4Node25Domains2Fast root4Node25Domains3Fast
    root4Node25Domains2_fast_eq root4Node25Domains3_fast_eq (by decide)
theorem root4Node25Step3_checked :
    checkReplacement table26 root4Node25Domains2 root4Node25Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node25Step3Chunk0_0_checked, root4Node25Step3Chunk0_1_checked, root4Node25Step3Chunk0_2_checked, root4Node25Step3Chunk0_3_checked, root4Node25Step3Chunk0_4_checked, root4Node25Step3Chunk0_5_checked, root4Node25Step3Chunk1_0_checked, root4Node25Step3Chunk1_1_checked, root4Node25Step3Chunk1_2_checked, root4Node25Step3Chunk1_3_checked, root4Node25Step3Chunk1_4_checked, root4Node25Step3Chunk1_5_checked, root4Node25Step3Chunk2_0_checked, root4Node25Step3Chunk2_1_checked, root4Node25Step3Chunk2_2_checked, root4Node25Step3Chunk2_3_checked, root4Node25Step3Chunk2_4_checked, root4Node25Step3Chunk2_5_checked, root4Node25Step3Chunk3_0_checked, root4Node25Step3Chunk3_1_checked, root4Node25Step3Chunk3_2_checked, root4Node25Step3Chunk3_3_checked, root4Node25Step3Chunk3_4_checked, root4Node25Step3Chunk3_5_checked, root4Node25Step3Chunk4_0_checked, root4Node25Step3Chunk4_1_checked, root4Node25Step3Chunk4_2_checked, root4Node25Step3Chunk4_3_checked, root4Node25Step3Chunk4_4_checked, root4Node25Step3Chunk4_5_checked, root4Node25Step3Chunk5_0_checked, root4Node25Step3Chunk5_1_checked, root4Node25Step3Chunk5_2_checked, root4Node25Step3Chunk5_3_checked, root4Node25Step3Chunk5_4_checked, root4Node25Step3Chunk5_5_checked, root4Node25Step3Chunk6_0_checked, root4Node25Step3Chunk6_1_checked, root4Node25Step3Chunk6_2_checked, root4Node25Step3Chunk6_3_checked, root4Node25Step3Chunk6_4_checked, root4Node25Step3Chunk6_5_checked, root4Node25Step3Chunk7_0_checked, root4Node25Step3Chunk7_1_checked, root4Node25Step3Chunk7_2_checked, root4Node25Step3Chunk7_3_checked, root4Node25Step3Chunk7_4_checked, root4Node25Step3Chunk7_5_checked, root4Node25Step3Chunk8_0_checked, root4Node25Step3Chunk8_1_checked, root4Node25Step3Chunk8_2_checked, root4Node25Step3Chunk8_3_checked, root4Node25Step3Chunk8_4_checked, root4Node25Step3Chunk8_5_checked, Bool.true_and]
  · decide
theorem root4Node25Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node25Domains3 (.output 12) = true := by decide
def root4Node26Domains0 : Domains 61 State := restrict root4Node0Domains4 9 (8,0)
def root4Node26Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 1 => some [(0,3),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(7,5),(8,1)]
  | 3 => some [(0,2),(1,5),(6,0),(6,5)]
  | 4 => some [(0,4),(1,1),(6,1),(7,1)]
  | 5 => some [(0,5),(1,2),(1,3),(3,2),(6,3),(7,2),(7,3)]
  | 6 => some [(2,0),(2,2),(4,0),(4,2)]
  | 7 => some [(3,3),(5,3),(7,3)]
  | 8 => some [(5,2),(5,5),(8,2),(8,5)]
  | 9 => some [(8,0)]
  | 10 => some [(4,3),(7,3),(8,3)]
  | 11 => some [(0,1),(0,2),(0,3),(6,0),(6,1),(6,5)]
  | 12 => some [(0,4),(1,1),(3,1),(5,1),(6,2)]
  | 13 => some [(0,1),(1,4),(3,4),(7,4)]
  | 14 => some [(0,5),(6,2),(6,3)]
  | 15 => some [(4,4),(7,2),(8,4)]
  | 16 => some [(1,4),(6,4),(7,4)]
  | 17 => some [(0,5),(1,2),(6,3)]
  | 18 => some [(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 19 => some [(1,0),(3,0),(5,0),(5,3),(7,0),(8,3)]
  | 20 => some [(2,1),(2,3),(2,5),(4,5),(8,5)]
  | 21 => some [(0,2),(1,0),(6,0)]
  | 22 => some [(1,1),(7,1)]
  | 23 => some [(4,1),(7,5)]
  | 24 => some [(0,2),(0,3),(6,0)]
  | 25 => some [(1,1),(3,1),(7,1),(8,1)]
  | 26 => some [(0,5),(1,2),(6,2),(7,2)]
  | 27 => some [(4,4),(7,4),(8,4)]
  | 28 => some [(0,0),(6,3),(6,4)]
  | 29 => some [(1,2),(3,2),(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(5,2),(8,2)]
  | 33 => some [(5,0),(5,3),(8,0)]
  | 34 => some [(4,5),(7,3),(8,3),(8,5)]
  | 35 => some [(4,1),(7,1),(8,1)]
  | 36 => some [(0,2),(1,5),(7,5)]
  | 37 => some [(0,3),(1,1),(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(1,4),(6,3),(6,4)]
  | 43 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 44 => some [(4,2),(7,0),(8,0)]
  | 45 => some [(5,3),(8,3)]
  | 46 => some [(5,5),(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(2,1),(7,1)]
  | 49 => some [(0,2),(1,5),(7,5)]
  | 50 => some [(1,2),(4,4),(5,4),(7,2),(8,4)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(1,3),(6,3)]
  | 53 => some [(4,4),(7,2),(8,2)]
  | 54 => some [(0,0),(4,0),(5,0),(8,0)]
  | 55 => some [(3,2),(4,5),(7,3)]
  | 56 => some [(4,1),(7,5),(8,1)]
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(0,4),(1,1),(7,1)]
  | 59 => some [(1,5),(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,1),(6,4)]
theorem root4Node26Domains0_fast_eq : root4Node26Domains0 = expandDomains root4Node26Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node26Domains0 v = expandDomains root4Node26Domains0Fast v from by decide) v
def root4Node26Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 1 => [(0,3),(1,1),(6,1),(7,1)]
  | 2 => [(4,1),(7,5)]
  | 3 => [(0,2),(6,0)]
  | 4 => [(0,4),(1,1),(6,1),(7,1)]
  | 5 => [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 6 => [(2,0),(2,2),(4,0)]
  | 7 => [(3,3),(7,3)]
  | 8 => [(5,2),(8,2)]
  | 9 => [(8,0)]
  | 10 => [(4,3),(7,3),(8,3)]
  | 11 => [(0,2),(0,3),(6,0),(6,1)]
  | 12 => [(1,1),(3,1),(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(1,4),(6,4)]
  | 17 => [(0,5),(1,2),(6,3)]
  | 18 => [(4,2),(5,2),(7,0),(8,2)]
  | 19 => [(5,0),(5,3),(8,3)]
  | 20 => [(4,5),(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3),(6,0)]
  | 25 => [(1,1),(3,1),(7,1),(8,1)]
  | 26 => [(0,5),(1,2),(6,2),(7,2)]
  | 27 => [(7,4),(8,4)]
  | 28 => [(0,0),(6,3)]
  | 29 => [(7,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2),(8,2)]
  | 33 => [(5,0),(5,3),(8,0)]
  | 34 => [(4,5),(7,3),(8,3),(8,5)]
  | 35 => [(4,1),(7,1),(8,1)]
  | 36 => [(0,2),(1,5)]
  | 37 => [(1,1),(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(7,4),(8,4)]
  | 42 => [(0,0),(1,4),(6,3),(6,4)]
  | 43 => [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 44 => [(7,0),(8,0)]
  | 45 => [(8,3)]
  | 46 => [(5,5),(8,5)]
  | 47 => [(1,0)]
  | 48 => [(2,1),(7,1)]
  | 49 => [(0,2),(1,5),(7,5)]
  | 50 => [(1,2),(4,4),(5,4),(7,2),(8,4)]
  | 51 => [(1,4),(7,4)]
  | 52 => [(0,5),(1,3),(6,3)]
  | 53 => [(4,4),(7,2),(8,2)]
  | 54 => [(0,0),(4,0),(5,0),(8,0)]
  | 55 => [(3,2),(4,5),(7,3)]
  | 56 => [(4,1),(7,5),(8,1)]
  | 57 => [(0,2),(6,0),(6,5)]
  | 58 => [(0,4),(1,1),(7,1)]
  | 59 => [(1,5),(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
def root4Node26Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 1 => some [(0,3),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(7,5)]
  | 3 => some [(0,2),(6,0)]
  | 4 => some [(0,4),(1,1),(6,1),(7,1)]
  | 5 => some [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 6 => some [(2,0),(2,2),(4,0)]
  | 7 => some [(3,3),(7,3)]
  | 8 => some [(5,2),(8,2)]
  | 9 => some [(8,0)]
  | 10 => some [(4,3),(7,3),(8,3)]
  | 11 => some [(0,2),(0,3),(6,0),(6,1)]
  | 12 => some [(1,1),(3,1),(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2),(6,3)]
  | 18 => some [(4,2),(5,2),(7,0),(8,2)]
  | 19 => some [(5,0),(5,3),(8,3)]
  | 20 => some [(4,5),(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(1,1),(3,1),(7,1),(8,1)]
  | 26 => some [(0,5),(1,2),(6,2),(7,2)]
  | 27 => some [(7,4),(8,4)]
  | 28 => some [(0,0),(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3),(8,0)]
  | 34 => some [(4,5),(7,3),(8,3),(8,5)]
  | 35 => some [(4,1),(7,1),(8,1)]
  | 36 => some [(0,2),(1,5)]
  | 37 => some [(1,1),(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(1,4),(6,3),(6,4)]
  | 43 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 44 => some [(7,0),(8,0)]
  | 45 => some [(8,3)]
  | 46 => some [(5,5),(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(2,1),(7,1)]
  | 49 => some [(0,2),(1,5),(7,5)]
  | 50 => some [(1,2),(4,4),(5,4),(7,2),(8,4)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(1,3),(6,3)]
  | 53 => some [(4,4),(7,2),(8,2)]
  | 54 => some [(0,0),(4,0),(5,0),(8,0)]
  | 55 => some [(3,2),(4,5),(7,3)]
  | 56 => some [(4,1),(7,5),(8,1)]
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(0,4),(1,1),(7,1)]
  | 59 => some [(1,5),(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,1),(6,4)]
theorem root4Node26Domains1_fast_eq : root4Node26Domains1 = expandDomains root4Node26Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node26Domains1 v = expandDomains root4Node26Domains1Fast v from by decide) v
theorem root4Node26Step1Chunk0_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_0⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk0_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_1⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk0_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_2⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk0_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_3⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk0_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_4⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk0_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_5⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk1_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_0⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk1_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_1⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk1_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_2⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk1_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_3⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk1_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_4⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk1_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_5⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk2_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_0⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk2_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_1⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk2_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_2⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk2_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_3⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk2_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_4⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk2_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_5⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk3_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_0⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk3_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_1⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk3_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_2⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk3_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_3⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk3_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_4⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk3_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_5⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk4_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_0⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk4_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_1⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk4_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_2⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk4_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_3⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk4_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_4⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk4_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_5⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk5_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_0⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk5_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_1⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk5_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_2⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk5_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_3⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk5_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_4⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk5_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_5⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk6_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_0⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk6_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_1⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk6_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_2⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk6_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_3⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk6_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_4⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk6_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_5⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk7_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_0⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk7_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_1⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk7_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_2⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk7_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_3⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk7_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_4⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk7_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_5⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk8_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_0⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk8_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_1⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk8_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_2⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk8_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_3⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk8_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_4⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1Chunk8_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_5⟩
      root4Node26Domains0 root4Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains0 root4Node26Domains1
    root4Node26Domains0Fast root4Node26Domains1Fast
    root4Node26Domains0_fast_eq root4Node26Domains1_fast_eq (by decide)
theorem root4Node26Step1_checked :
    checkReplacement table21 root4Node26Domains0 root4Node26Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node26Step1Chunk0_0_checked, root4Node26Step1Chunk0_1_checked, root4Node26Step1Chunk0_2_checked, root4Node26Step1Chunk0_3_checked, root4Node26Step1Chunk0_4_checked, root4Node26Step1Chunk0_5_checked, root4Node26Step1Chunk1_0_checked, root4Node26Step1Chunk1_1_checked, root4Node26Step1Chunk1_2_checked, root4Node26Step1Chunk1_3_checked, root4Node26Step1Chunk1_4_checked, root4Node26Step1Chunk1_5_checked, root4Node26Step1Chunk2_0_checked, root4Node26Step1Chunk2_1_checked, root4Node26Step1Chunk2_2_checked, root4Node26Step1Chunk2_3_checked, root4Node26Step1Chunk2_4_checked, root4Node26Step1Chunk2_5_checked, root4Node26Step1Chunk3_0_checked, root4Node26Step1Chunk3_1_checked, root4Node26Step1Chunk3_2_checked, root4Node26Step1Chunk3_3_checked, root4Node26Step1Chunk3_4_checked, root4Node26Step1Chunk3_5_checked, root4Node26Step1Chunk4_0_checked, root4Node26Step1Chunk4_1_checked, root4Node26Step1Chunk4_2_checked, root4Node26Step1Chunk4_3_checked, root4Node26Step1Chunk4_4_checked, root4Node26Step1Chunk4_5_checked, root4Node26Step1Chunk5_0_checked, root4Node26Step1Chunk5_1_checked, root4Node26Step1Chunk5_2_checked, root4Node26Step1Chunk5_3_checked, root4Node26Step1Chunk5_4_checked, root4Node26Step1Chunk5_5_checked, root4Node26Step1Chunk6_0_checked, root4Node26Step1Chunk6_1_checked, root4Node26Step1Chunk6_2_checked, root4Node26Step1Chunk6_3_checked, root4Node26Step1Chunk6_4_checked, root4Node26Step1Chunk6_5_checked, root4Node26Step1Chunk7_0_checked, root4Node26Step1Chunk7_1_checked, root4Node26Step1Chunk7_2_checked, root4Node26Step1Chunk7_3_checked, root4Node26Step1Chunk7_4_checked, root4Node26Step1Chunk7_5_checked, root4Node26Step1Chunk8_0_checked, root4Node26Step1Chunk8_1_checked, root4Node26Step1Chunk8_2_checked, root4Node26Step1Chunk8_3_checked, root4Node26Step1Chunk8_4_checked, root4Node26Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node26Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 1 => [(0,3),(1,1),(6,1),(7,1)]
  | 2 => [(4,1),(7,5)]
  | 3 => [(0,2),(6,0)]
  | 4 => [(1,1),(7,1)]
  | 5 => [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 6 => [(2,0),(2,2),(4,0)]
  | 7 => [(3,3),(7,3)]
  | 8 => [(5,2),(8,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3),(8,3)]
  | 11 => [(0,2),(0,3),(6,0),(6,1)]
  | 12 => [(1,1),(3,1),(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(1,4),(6,4)]
  | 17 => [(0,5),(1,2)]
  | 18 => [(4,2),(5,2),(7,0),(8,2)]
  | 19 => [(5,0),(5,3),(8,3)]
  | 20 => [(4,5),(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3),(6,0)]
  | 25 => [(7,1),(8,1)]
  | 26 => [(0,5),(1,2),(6,2),(7,2)]
  | 27 => [(7,4),(8,4)]
  | 28 => [(0,0),(6,3)]
  | 29 => [(7,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2),(8,2)]
  | 33 => [(5,0),(5,3),(8,0)]
  | 34 => [(4,5),(7,3),(8,5)]
  | 35 => [(4,1),(7,1),(8,1)]
  | 36 => [(0,2),(1,5)]
  | 37 => [(1,1),(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(7,4),(8,4)]
  | 42 => [(0,0),(6,3),(6,4)]
  | 43 => [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 44 => [(7,0),(8,0)]
  | 45 => [(8,3)]
  | 46 => [(5,5),(8,5)]
  | 47 => [(1,0)]
  | 48 => [(2,1),(7,1)]
  | 49 => [(0,2),(1,5),(7,5)]
  | 50 => [(1,2),(4,4),(5,4),(7,2),(8,4)]
  | 51 => [(1,4),(7,4)]
  | 52 => [(0,5),(1,3),(6,3)]
  | 53 => [(4,4),(7,2),(8,2)]
  | 54 => [(0,0),(4,0),(5,0),(8,0)]
  | 55 => [(3,2),(4,5),(7,3)]
  | 56 => [(4,1),(7,5),(8,1)]
  | 57 => [(0,2),(6,0),(6,5)]
  | 58 => [(0,4),(1,1),(7,1)]
  | 59 => [(1,5),(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
def root4Node26Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 1 => some [(0,3),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(7,5)]
  | 3 => some [(0,2),(6,0)]
  | 4 => some [(1,1),(7,1)]
  | 5 => some [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 6 => some [(2,0),(2,2),(4,0)]
  | 7 => some [(3,3),(7,3)]
  | 8 => some [(5,2),(8,2)]
  | 9 => some [(8,0)]
  | 10 => some [(7,3),(8,3)]
  | 11 => some [(0,2),(0,3),(6,0),(6,1)]
  | 12 => some [(1,1),(3,1),(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(4,2),(5,2),(7,0),(8,2)]
  | 19 => some [(5,0),(5,3),(8,3)]
  | 20 => some [(4,5),(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(7,1),(8,1)]
  | 26 => some [(0,5),(1,2),(6,2),(7,2)]
  | 27 => some [(7,4),(8,4)]
  | 28 => some [(0,0),(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3),(8,0)]
  | 34 => some [(4,5),(7,3),(8,5)]
  | 35 => some [(4,1),(7,1),(8,1)]
  | 36 => some [(0,2),(1,5)]
  | 37 => some [(1,1),(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(6,3),(6,4)]
  | 43 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 44 => some [(7,0),(8,0)]
  | 45 => some [(8,3)]
  | 46 => some [(5,5),(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(2,1),(7,1)]
  | 49 => some [(0,2),(1,5),(7,5)]
  | 50 => some [(1,2),(4,4),(5,4),(7,2),(8,4)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(1,3),(6,3)]
  | 53 => some [(4,4),(7,2),(8,2)]
  | 54 => some [(0,0),(4,0),(5,0),(8,0)]
  | 55 => some [(3,2),(4,5),(7,3)]
  | 56 => some [(4,1),(7,5),(8,1)]
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(0,4),(1,1),(7,1)]
  | 59 => some [(1,5),(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,1),(6,4)]
theorem root4Node26Domains2_fast_eq : root4Node26Domains2 = expandDomains root4Node26Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node26Domains2 v = expandDomains root4Node26Domains2Fast v from by decide) v
theorem root4Node26Step2Chunk0_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_0⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk0_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_1⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk0_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_2⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk0_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_3⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk0_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_4⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk0_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_5⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk1_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_0⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk1_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_1⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk1_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_2⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk1_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_3⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk1_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_4⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk1_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_5⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk2_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_0⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk2_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_1⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk2_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_2⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk2_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_3⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk2_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_4⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk2_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_5⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk3_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_0⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk3_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_1⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk3_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_2⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk3_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_3⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk3_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_4⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk3_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_5⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk4_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_0⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk4_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_1⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk4_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_2⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk4_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_3⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk4_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_4⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk4_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_5⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk5_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_0⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk5_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_1⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk5_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_2⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk5_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_3⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk5_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_4⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk5_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_5⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk6_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_0⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk6_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_1⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk6_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_2⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk6_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_3⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk6_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_4⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk6_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_5⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk7_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_0⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk7_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_1⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk7_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_2⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk7_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_3⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk7_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_4⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk7_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_5⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk8_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_0⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk8_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_1⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk8_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_2⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk8_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_3⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk8_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_4⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2Chunk8_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_5⟩
      root4Node26Domains1 root4Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains1 root4Node26Domains2
    root4Node26Domains1Fast root4Node26Domains2Fast
    root4Node26Domains1_fast_eq root4Node26Domains2_fast_eq (by decide)
theorem root4Node26Step2_checked :
    checkReplacement table16 root4Node26Domains1 root4Node26Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node26Step2Chunk0_0_checked, root4Node26Step2Chunk0_1_checked, root4Node26Step2Chunk0_2_checked, root4Node26Step2Chunk0_3_checked, root4Node26Step2Chunk0_4_checked, root4Node26Step2Chunk0_5_checked, root4Node26Step2Chunk1_0_checked, root4Node26Step2Chunk1_1_checked, root4Node26Step2Chunk1_2_checked, root4Node26Step2Chunk1_3_checked, root4Node26Step2Chunk1_4_checked, root4Node26Step2Chunk1_5_checked, root4Node26Step2Chunk2_0_checked, root4Node26Step2Chunk2_1_checked, root4Node26Step2Chunk2_2_checked, root4Node26Step2Chunk2_3_checked, root4Node26Step2Chunk2_4_checked, root4Node26Step2Chunk2_5_checked, root4Node26Step2Chunk3_0_checked, root4Node26Step2Chunk3_1_checked, root4Node26Step2Chunk3_2_checked, root4Node26Step2Chunk3_3_checked, root4Node26Step2Chunk3_4_checked, root4Node26Step2Chunk3_5_checked, root4Node26Step2Chunk4_0_checked, root4Node26Step2Chunk4_1_checked, root4Node26Step2Chunk4_2_checked, root4Node26Step2Chunk4_3_checked, root4Node26Step2Chunk4_4_checked, root4Node26Step2Chunk4_5_checked, root4Node26Step2Chunk5_0_checked, root4Node26Step2Chunk5_1_checked, root4Node26Step2Chunk5_2_checked, root4Node26Step2Chunk5_3_checked, root4Node26Step2Chunk5_4_checked, root4Node26Step2Chunk5_5_checked, root4Node26Step2Chunk6_0_checked, root4Node26Step2Chunk6_1_checked, root4Node26Step2Chunk6_2_checked, root4Node26Step2Chunk6_3_checked, root4Node26Step2Chunk6_4_checked, root4Node26Step2Chunk6_5_checked, root4Node26Step2Chunk7_0_checked, root4Node26Step2Chunk7_1_checked, root4Node26Step2Chunk7_2_checked, root4Node26Step2Chunk7_3_checked, root4Node26Step2Chunk7_4_checked, root4Node26Step2Chunk7_5_checked, root4Node26Step2Chunk8_0_checked, root4Node26Step2Chunk8_1_checked, root4Node26Step2Chunk8_2_checked, root4Node26Step2Chunk8_3_checked, root4Node26Step2Chunk8_4_checked, root4Node26Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node26Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 1 => [(0,3),(1,1),(6,1),(7,1)]
  | 2 => [(4,1),(7,5)]
  | 3 => [(0,2),(6,0)]
  | 4 => [(1,1),(7,1)]
  | 5 => [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 6 => [(2,0),(2,2),(4,0)]
  | 7 => [(3,3),(7,3)]
  | 8 => [(5,2),(8,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3),(8,3)]
  | 11 => [(0,2),(0,3),(6,0),(6,1)]
  | 12 => [(1,1),(3,1),(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(1,4),(6,4)]
  | 17 => [(0,5),(1,2)]
  | 18 => [(4,2),(5,2),(7,0),(8,2)]
  | 19 => [(5,0),(5,3),(8,3)]
  | 20 => [(4,5),(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3),(6,0)]
  | 25 => [(7,1),(8,1)]
  | 26 => [(1,2),(6,2),(7,2)]
  | 27 => [(7,4),(8,4)]
  | 28 => [(0,0),(6,3)]
  | 29 => [(7,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2),(8,2)]
  | 33 => [(5,0),(5,3),(8,0)]
  | 34 => [(4,5),(7,3),(8,5)]
  | 35 => [(4,1),(7,1),(8,1)]
  | 36 => [(0,2),(1,5)]
  | 37 => [(1,1),(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(7,4),(8,4)]
  | 42 => [(0,0),(6,3),(6,4)]
  | 43 => [(4,5),(5,2),(5,5),(8,5)]
  | 44 => [(7,0),(8,0)]
  | 45 => [(8,3)]
  | 46 => [(5,5),(8,5)]
  | 47 => [(1,0)]
  | 48 => [(2,1),(7,1)]
  | 49 => [(0,2),(1,5),(7,5)]
  | 50 => [(4,4),(5,4),(7,2),(8,4)]
  | 51 => [(1,4),(7,4)]
  | 52 => [(0,5),(1,3),(6,3)]
  | 53 => [(4,4),(7,2),(8,2)]
  | 54 => [(0,0),(4,0),(5,0),(8,0)]
  | 55 => [(3,2),(4,5),(7,3)]
  | 56 => [(4,1),(7,5),(8,1)]
  | 57 => [(0,2),(6,0),(6,5)]
  | 58 => [(0,4),(1,1),(7,1)]
  | 59 => [(1,5),(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
def root4Node26Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 1 => some [(0,3),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(7,5)]
  | 3 => some [(0,2),(6,0)]
  | 4 => some [(1,1),(7,1)]
  | 5 => some [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 6 => some [(2,0),(2,2),(4,0)]
  | 7 => some [(3,3),(7,3)]
  | 8 => some [(5,2),(8,2)]
  | 9 => some [(8,0)]
  | 10 => some [(7,3),(8,3)]
  | 11 => some [(0,2),(0,3),(6,0),(6,1)]
  | 12 => some [(1,1),(3,1),(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(4,2),(5,2),(7,0),(8,2)]
  | 19 => some [(5,0),(5,3),(8,3)]
  | 20 => some [(4,5),(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(7,1),(8,1)]
  | 26 => some [(1,2),(6,2),(7,2)]
  | 27 => some [(7,4),(8,4)]
  | 28 => some [(0,0),(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3),(8,0)]
  | 34 => some [(4,5),(7,3),(8,5)]
  | 35 => some [(4,1),(7,1),(8,1)]
  | 36 => some [(0,2),(1,5)]
  | 37 => some [(1,1),(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(6,3),(6,4)]
  | 43 => some [(4,5),(5,2),(5,5),(8,5)]
  | 44 => some [(7,0),(8,0)]
  | 45 => some [(8,3)]
  | 46 => some [(5,5),(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(2,1),(7,1)]
  | 49 => some [(0,2),(1,5),(7,5)]
  | 50 => some [(4,4),(5,4),(7,2),(8,4)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(1,3),(6,3)]
  | 53 => some [(4,4),(7,2),(8,2)]
  | 54 => some [(0,0),(4,0),(5,0),(8,0)]
  | 55 => some [(3,2),(4,5),(7,3)]
  | 56 => some [(4,1),(7,5),(8,1)]
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(0,4),(1,1),(7,1)]
  | 59 => some [(1,5),(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,1),(6,4)]
theorem root4Node26Domains3_fast_eq : root4Node26Domains3 = expandDomains root4Node26Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node26Domains3 v = expandDomains root4Node26Domains3Fast v from by decide) v
theorem root4Node26Step3Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root4Node26Domains2 root4Node26Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node26Domains2 root4Node26Domains3
    root4Node26Domains2Fast root4Node26Domains3Fast
    root4Node26Domains2_fast_eq root4Node26Domains3_fast_eq (by decide)
theorem root4Node26Step3_checked :
    checkReplacement table26 root4Node26Domains2 root4Node26Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node26Step3Chunk0_0_checked, root4Node26Step3Chunk0_1_checked, root4Node26Step3Chunk0_2_checked, root4Node26Step3Chunk0_3_checked, root4Node26Step3Chunk0_4_checked, root4Node26Step3Chunk0_5_checked, root4Node26Step3Chunk1_0_checked, root4Node26Step3Chunk1_1_checked, root4Node26Step3Chunk1_2_checked, root4Node26Step3Chunk1_3_checked, root4Node26Step3Chunk1_4_checked, root4Node26Step3Chunk1_5_checked, root4Node26Step3Chunk2_0_checked, root4Node26Step3Chunk2_1_checked, root4Node26Step3Chunk2_2_checked, root4Node26Step3Chunk2_3_checked, root4Node26Step3Chunk2_4_checked, root4Node26Step3Chunk2_5_checked, root4Node26Step3Chunk3_0_checked, root4Node26Step3Chunk3_1_checked, root4Node26Step3Chunk3_2_checked, root4Node26Step3Chunk3_3_checked, root4Node26Step3Chunk3_4_checked, root4Node26Step3Chunk3_5_checked, root4Node26Step3Chunk4_0_checked, root4Node26Step3Chunk4_1_checked, root4Node26Step3Chunk4_2_checked, root4Node26Step3Chunk4_3_checked, root4Node26Step3Chunk4_4_checked, root4Node26Step3Chunk4_5_checked, root4Node26Step3Chunk5_0_checked, root4Node26Step3Chunk5_1_checked, root4Node26Step3Chunk5_2_checked, root4Node26Step3Chunk5_3_checked, root4Node26Step3Chunk5_4_checked, root4Node26Step3Chunk5_5_checked, root4Node26Step3Chunk6_0_checked, root4Node26Step3Chunk6_1_checked, root4Node26Step3Chunk6_2_checked, root4Node26Step3Chunk6_3_checked, root4Node26Step3Chunk6_4_checked, root4Node26Step3Chunk6_5_checked, root4Node26Step3Chunk7_0_checked, root4Node26Step3Chunk7_1_checked, root4Node26Step3Chunk7_2_checked, root4Node26Step3Chunk7_3_checked, root4Node26Step3Chunk7_4_checked, root4Node26Step3Chunk7_5_checked, root4Node26Step3Chunk8_0_checked, root4Node26Step3Chunk8_1_checked, root4Node26Step3Chunk8_2_checked, root4Node26Step3Chunk8_3_checked, root4Node26Step3Chunk8_4_checked, root4Node26Step3Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
