module

public import SpectreFinite.RadiusFourRoot7Part49
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable23
public import SpectreFinite.RadiusFourTable36
public import SpectreFinite.RadiusFourTable39
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node149Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(8,0)]
  | 17 => [(7,3)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(8,5)]
  | 27 => [(7,0)]
  | 28 => [(8,3)]
  | 29 => [(8,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(7,5)]
  | 33 => [(0,3)]
  | 34 => [(8,1)]
  | 35 => [(7,2)]
  | 36 => [(7,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(1,3)]
  | 41 => [(4,2)]
  | 42 => [(5,3)]
  | 43 => [(4,1)]
  | 44 => [(0,2)]
  | 45 => [(1,1)]
  | 46 => [(8,1)]
  | 47 => [(6,5)]
  | 48 => [(0,4)]
  | 49 => [(1,4),(3,4)]
  | 50 => [(5,2)]
  | 51 => [(8,0)]
  | 52 => [(8,3)]
  | 53 => [(5,5)]
  | 54 => [(3,0),(7,0)]
  | 55 => [(2,3),(2,5)]
  | 56 => [(8,4)]
  | 57 => [(1,4)]
  | 58 => [(0,5)]
  | 59 => [(4,4)]
  | _ => [(0,0),(6,4)]
def root7Node149Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(8,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(8,1)]
  | 35 => some [(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(4,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(8,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(1,4),(3,4)]
  | 50 => some [(5,2)]
  | 51 => some [(8,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5)]
  | 54 => some [(3,0),(7,0)]
  | 55 => some [(2,3),(2,5)]
  | 56 => some [(8,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(4,4)]
  | _ => some [(0,0),(6,4)]
theorem root7Node149Domains2_fast_eq : root7Node149Domains2 = expandDomains root7Node149Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node149Domains2 v = expandDomains root7Node149Domains2Fast v from by decide) v
theorem root7Node149Step2Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root7Node149Domains1 root7Node149Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node149Domains1 root7Node149Domains2
    root7Node149Domains1Fast root7Node149Domains2Fast
    root7Node149Domains1_fast_eq root7Node149Domains2_fast_eq (by decide)
theorem root7Node149Step2_checked :
    checkReplacement table36 root7Node149Domains1 root7Node149Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node149Step2Chunk0_0_checked, root7Node149Step2Chunk0_1_checked, root7Node149Step2Chunk0_2_checked, root7Node149Step2Chunk0_3_checked, root7Node149Step2Chunk0_4_checked, root7Node149Step2Chunk0_5_checked, root7Node149Step2Chunk1_0_checked, root7Node149Step2Chunk1_1_checked, root7Node149Step2Chunk1_2_checked, root7Node149Step2Chunk1_3_checked, root7Node149Step2Chunk1_4_checked, root7Node149Step2Chunk1_5_checked, root7Node149Step2Chunk2_0_checked, root7Node149Step2Chunk2_1_checked, root7Node149Step2Chunk2_2_checked, root7Node149Step2Chunk2_3_checked, root7Node149Step2Chunk2_4_checked, root7Node149Step2Chunk2_5_checked, root7Node149Step2Chunk3_0_checked, root7Node149Step2Chunk3_1_checked, root7Node149Step2Chunk3_2_checked, root7Node149Step2Chunk3_3_checked, root7Node149Step2Chunk3_4_checked, root7Node149Step2Chunk3_5_checked, root7Node149Step2Chunk4_0_checked, root7Node149Step2Chunk4_1_checked, root7Node149Step2Chunk4_2_checked, root7Node149Step2Chunk4_3_checked, root7Node149Step2Chunk4_4_checked, root7Node149Step2Chunk4_5_checked, root7Node149Step2Chunk5_0_checked, root7Node149Step2Chunk5_1_checked, root7Node149Step2Chunk5_2_checked, root7Node149Step2Chunk5_3_checked, root7Node149Step2Chunk5_4_checked, root7Node149Step2Chunk5_5_checked, root7Node149Step2Chunk6_0_checked, root7Node149Step2Chunk6_1_checked, root7Node149Step2Chunk6_2_checked, root7Node149Step2Chunk6_3_checked, root7Node149Step2Chunk6_4_checked, root7Node149Step2Chunk6_5_checked, root7Node149Step2Chunk7_0_checked, root7Node149Step2Chunk7_1_checked, root7Node149Step2Chunk7_2_checked, root7Node149Step2Chunk7_3_checked, root7Node149Step2Chunk7_4_checked, root7Node149Step2Chunk7_5_checked, root7Node149Step2Chunk8_0_checked, root7Node149Step2Chunk8_1_checked, root7Node149Step2Chunk8_2_checked, root7Node149Step2Chunk8_3_checked, root7Node149Step2Chunk8_4_checked, root7Node149Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node150Domains0 : Domains 61 State := restrict root7Node149Domains2 49 (1,4)
def root7Node150Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(8,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(8,1)]
  | 35 => some [(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(4,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(8,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(1,4)]
  | 50 => some [(5,2)]
  | 51 => some [(8,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5)]
  | 54 => some [(3,0),(7,0)]
  | 55 => some [(2,3),(2,5)]
  | 56 => some [(8,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(4,4)]
  | _ => some [(0,0),(6,4)]
theorem root7Node150Domains0_fast_eq : root7Node150Domains0 = expandDomains root7Node150Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node150Domains0 v = expandDomains root7Node150Domains0Fast v from by decide) v
def root7Node150Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(8,0)]
  | 17 => [(7,3)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(8,5)]
  | 27 => [(7,0)]
  | 28 => [(8,3)]
  | 29 => [(8,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(7,5)]
  | 33 => [(0,3)]
  | 34 => [(8,1)]
  | 35 => [(7,2)]
  | 36 => [(7,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(1,3)]
  | 41 => [(4,2)]
  | 42 => [(5,3)]
  | 43 => [(4,1)]
  | 44 => [(0,2)]
  | 45 => [(1,1)]
  | 46 => [(8,1)]
  | 47 => [(6,5)]
  | 48 => [(0,4)]
  | 49 => [(1,4)]
  | 50 => [(5,2)]
  | 51 => [(8,0)]
  | 52 => [(8,3)]
  | 53 => [(5,5)]
  | 54 => [(3,0)]
  | 55 => [(2,5)]
  | 56 => [(8,4)]
  | 57 => [(1,4)]
  | 58 => [(0,5)]
  | 59 => [(4,4)]
  | _ => [(0,0)]
def root7Node150Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(8,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(8,1)]
  | 35 => some [(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(4,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(8,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(1,4)]
  | 50 => some [(5,2)]
  | 51 => some [(8,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5)]
  | 54 => some [(3,0)]
  | 55 => some [(2,5)]
  | 56 => some [(8,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(4,4)]
  | _ => some [(0,0)]
theorem root7Node150Domains1_fast_eq : root7Node150Domains1 = expandDomains root7Node150Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node150Domains1 v = expandDomains root7Node150Domains1Fast v from by decide) v
theorem root7Node150Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root7Node150Domains0 root7Node150Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node150Domains0 root7Node150Domains1
    root7Node150Domains0Fast root7Node150Domains1Fast
    root7Node150Domains0_fast_eq root7Node150Domains1_fast_eq (by decide)
theorem root7Node150Step1_checked :
    checkReplacement table39 root7Node150Domains0 root7Node150Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node150Step1Chunk0_0_checked, root7Node150Step1Chunk0_1_checked, root7Node150Step1Chunk0_2_checked, root7Node150Step1Chunk0_3_checked, root7Node150Step1Chunk0_4_checked, root7Node150Step1Chunk0_5_checked, root7Node150Step1Chunk1_0_checked, root7Node150Step1Chunk1_1_checked, root7Node150Step1Chunk1_2_checked, root7Node150Step1Chunk1_3_checked, root7Node150Step1Chunk1_4_checked, root7Node150Step1Chunk1_5_checked, root7Node150Step1Chunk2_0_checked, root7Node150Step1Chunk2_1_checked, root7Node150Step1Chunk2_2_checked, root7Node150Step1Chunk2_3_checked, root7Node150Step1Chunk2_4_checked, root7Node150Step1Chunk2_5_checked, root7Node150Step1Chunk3_0_checked, root7Node150Step1Chunk3_1_checked, root7Node150Step1Chunk3_2_checked, root7Node150Step1Chunk3_3_checked, root7Node150Step1Chunk3_4_checked, root7Node150Step1Chunk3_5_checked, root7Node150Step1Chunk4_0_checked, root7Node150Step1Chunk4_1_checked, root7Node150Step1Chunk4_2_checked, root7Node150Step1Chunk4_3_checked, root7Node150Step1Chunk4_4_checked, root7Node150Step1Chunk4_5_checked, root7Node150Step1Chunk5_0_checked, root7Node150Step1Chunk5_1_checked, root7Node150Step1Chunk5_2_checked, root7Node150Step1Chunk5_3_checked, root7Node150Step1Chunk5_4_checked, root7Node150Step1Chunk5_5_checked, root7Node150Step1Chunk6_0_checked, root7Node150Step1Chunk6_1_checked, root7Node150Step1Chunk6_2_checked, root7Node150Step1Chunk6_3_checked, root7Node150Step1Chunk6_4_checked, root7Node150Step1Chunk6_5_checked, root7Node150Step1Chunk7_0_checked, root7Node150Step1Chunk7_1_checked, root7Node150Step1Chunk7_2_checked, root7Node150Step1Chunk7_3_checked, root7Node150Step1Chunk7_4_checked, root7Node150Step1Chunk7_5_checked, root7Node150Step1Chunk8_0_checked, root7Node150Step1Chunk8_1_checked, root7Node150Step1Chunk8_2_checked, root7Node150Step1Chunk8_3_checked, root7Node150Step1Chunk8_4_checked, root7Node150Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root7Node150Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node150Domains1 (.output 74) = true := by decide
def root7Node151Domains0 : Domains 61 State := restrict root7Node149Domains2 49 (3,4)
def root7Node151Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(8,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(8,1)]
  | 35 => some [(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(4,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(8,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(3,4)]
  | 50 => some [(5,2)]
  | 51 => some [(8,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5)]
  | 54 => some [(3,0),(7,0)]
  | 55 => some [(2,3),(2,5)]
  | 56 => some [(8,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(4,4)]
  | _ => some [(0,0),(6,4)]
theorem root7Node151Domains0_fast_eq : root7Node151Domains0 = expandDomains root7Node151Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node151Domains0 v = expandDomains root7Node151Domains0Fast v from by decide) v
def root7Node151Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(8,0)]
  | 17 => [(7,3)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(8,5)]
  | 27 => [(7,0)]
  | 28 => [(8,3)]
  | 29 => [(8,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(7,5)]
  | 33 => [(0,3)]
  | 34 => [(8,1)]
  | 35 => [(7,2)]
  | 36 => [(7,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(1,3)]
  | 41 => [(4,2)]
  | 42 => [(5,3)]
  | 43 => [(4,1)]
  | 44 => [(0,2)]
  | 45 => [(1,1)]
  | 46 => [(8,1)]
  | 47 => [(6,5)]
  | 48 => [(0,4)]
  | 49 => [(3,4)]
  | 50 => [(5,2)]
  | 51 => [(8,0)]
  | 52 => [(8,3)]
  | 53 => [(5,5)]
  | 54 => [(7,0)]
  | 55 => [(2,3)]
  | 56 => [(8,4)]
  | 57 => [(1,4)]
  | 58 => [(0,5)]
  | 59 => [(4,4)]
  | _ => [(6,4)]
def root7Node151Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(8,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(8,1)]
  | 35 => some [(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(4,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(8,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(3,4)]
  | 50 => some [(5,2)]
  | 51 => some [(8,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5)]
  | 54 => some [(7,0)]
  | 55 => some [(2,3)]
  | 56 => some [(8,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(4,4)]
  | _ => some [(6,4)]
theorem root7Node151Domains1_fast_eq : root7Node151Domains1 = expandDomains root7Node151Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node151Domains1 v = expandDomains root7Node151Domains1Fast v from by decide) v
theorem root7Node151Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root7Node151Domains0 root7Node151Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node151Domains0 root7Node151Domains1
    root7Node151Domains0Fast root7Node151Domains1Fast
    root7Node151Domains0_fast_eq root7Node151Domains1_fast_eq (by decide)
theorem root7Node151Step1_checked :
    checkReplacement table39 root7Node151Domains0 root7Node151Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node151Step1Chunk0_0_checked, root7Node151Step1Chunk0_1_checked, root7Node151Step1Chunk0_2_checked, root7Node151Step1Chunk0_3_checked, root7Node151Step1Chunk0_4_checked, root7Node151Step1Chunk0_5_checked, root7Node151Step1Chunk1_0_checked, root7Node151Step1Chunk1_1_checked, root7Node151Step1Chunk1_2_checked, root7Node151Step1Chunk1_3_checked, root7Node151Step1Chunk1_4_checked, root7Node151Step1Chunk1_5_checked, root7Node151Step1Chunk2_0_checked, root7Node151Step1Chunk2_1_checked, root7Node151Step1Chunk2_2_checked, root7Node151Step1Chunk2_3_checked, root7Node151Step1Chunk2_4_checked, root7Node151Step1Chunk2_5_checked, root7Node151Step1Chunk3_0_checked, root7Node151Step1Chunk3_1_checked, root7Node151Step1Chunk3_2_checked, root7Node151Step1Chunk3_3_checked, root7Node151Step1Chunk3_4_checked, root7Node151Step1Chunk3_5_checked, root7Node151Step1Chunk4_0_checked, root7Node151Step1Chunk4_1_checked, root7Node151Step1Chunk4_2_checked, root7Node151Step1Chunk4_3_checked, root7Node151Step1Chunk4_4_checked, root7Node151Step1Chunk4_5_checked, root7Node151Step1Chunk5_0_checked, root7Node151Step1Chunk5_1_checked, root7Node151Step1Chunk5_2_checked, root7Node151Step1Chunk5_3_checked, root7Node151Step1Chunk5_4_checked, root7Node151Step1Chunk5_5_checked, root7Node151Step1Chunk6_0_checked, root7Node151Step1Chunk6_1_checked, root7Node151Step1Chunk6_2_checked, root7Node151Step1Chunk6_3_checked, root7Node151Step1Chunk6_4_checked, root7Node151Step1Chunk6_5_checked, root7Node151Step1Chunk7_0_checked, root7Node151Step1Chunk7_1_checked, root7Node151Step1Chunk7_2_checked, root7Node151Step1Chunk7_3_checked, root7Node151Step1Chunk7_4_checked, root7Node151Step1Chunk7_5_checked, root7Node151Step1Chunk8_0_checked, root7Node151Step1Chunk8_1_checked, root7Node151Step1Chunk8_2_checked, root7Node151Step1Chunk8_3_checked, root7Node151Step1Chunk8_4_checked, root7Node151Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root7Node151Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node151Domains1 (.output 75) = true := by decide
def root7Node152Domains0 : Domains 61 State := restrict root7Node136Domains3 3 (6,4)
def root7Node152Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(0,5),(1,2)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3),(6,0)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2),(8,2)]
  | 16 => some [(5,0),(5,3),(8,0)]
  | 17 => some [(4,5),(7,3),(8,5)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(3,4),(5,4)]
  | 24 => some [(0,0),(6,3),(6,4)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(4,5),(5,2),(5,5),(8,5)]
  | 27 => some [(7,0),(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(2,3),(4,3)]
  | 32 => some [(0,2),(1,5),(3,5),(7,5)]
  | 33 => some [(0,3),(1,1),(6,1)]
  | 34 => some [(4,1),(8,1)]
  | 35 => some [(4,4),(5,4),(7,2),(8,4)]
  | 36 => some [(1,4),(7,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(6,4),(7,4)]
  | 40 => some [(0,5),(1,2),(1,3),(6,3)]
  | 41 => some [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 42 => some [(1,3),(3,3),(5,3),(7,3)]
  | 43 => some [(4,1),(7,5)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(0,3),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 49 => some [(0,1),(1,4),(3,4),(6,5)]
  | 50 => some [(5,2),(8,2)]
  | 51 => some [(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(4,2),(5,2),(5,5),(8,2)]
  | 54 => some [(3,0),(5,0),(5,3),(7,0)]
  | 55 => some [(2,3),(2,5),(4,5),(8,5)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(1,4),(6,4)]
  | 58 => some [(0,5),(1,2)]
  | 59 => some [(4,4),(7,4),(8,4)]
  | _ => some [(0,0),(1,3),(6,3),(6,4)]
theorem root7Node152Domains0_fast_eq : root7Node152Domains0 = expandDomains root7Node152Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node152Domains0 v = expandDomains root7Node152Domains0Fast v from by decide) v
def root7Node152Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(4,5),(8,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(0,0),(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(0,2),(1,5)]
  | 19 => [(1,1),(6,1)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(3,4)]
  | 24 => [(6,3)]
  | 25 => [(7,2)]
  | 26 => [(4,5),(5,2),(5,5),(8,5)]
  | 27 => [(7,0),(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(7,0)]
  | 31 => [(2,3)]
  | 32 => [(0,2)]
  | 33 => [(1,1)]
  | 34 => [(4,1)]
  | 35 => [(4,4),(5,4),(7,2),(8,4)]
  | 36 => [(1,4),(7,4)]
  | 37 => [(0,5),(6,3)]
  | 38 => [(4,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(4,0)]
  | 42 => [(7,3)]
  | 43 => [(4,1),(7,5)]
  | 44 => [(0,2),(6,0)]
  | 45 => [(1,1),(7,1)]
  | 46 => [(7,5)]
  | 47 => [(0,3)]
  | 48 => [(5,1)]
  | 49 => [(0,1)]
  | 50 => [(5,2),(8,2)]
  | 51 => [(8,0)]
  | 52 => [(7,3),(8,3)]
  | 53 => [(4,2),(5,2),(5,5),(8,2)]
  | 54 => [(3,0),(5,0),(5,3),(7,0)]
  | 55 => [(2,3),(2,5),(4,5),(8,5)]
  | 56 => [(5,4),(8,4)]
  | 57 => [(1,4),(6,4)]
  | 58 => [(0,5),(1,2)]
  | 59 => [(4,4),(7,4),(8,4)]
  | _ => [(0,0),(1,3),(6,3),(6,4)]
def root7Node152Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(3,4)]
  | 24 => some [(6,3)]
  | 25 => some [(7,2)]
  | 26 => some [(4,5),(5,2),(5,5),(8,5)]
  | 27 => some [(7,0),(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,0)]
  | 31 => some [(2,3)]
  | 32 => some [(0,2)]
  | 33 => some [(1,1)]
  | 34 => some [(4,1)]
  | 35 => some [(4,4),(5,4),(7,2),(8,4)]
  | 36 => some [(1,4),(7,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(4,1),(7,5)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(5,2),(8,2)]
  | 51 => some [(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(4,2),(5,2),(5,5),(8,2)]
  | 54 => some [(3,0),(5,0),(5,3),(7,0)]
  | 55 => some [(2,3),(2,5),(4,5),(8,5)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(1,4),(6,4)]
  | 58 => some [(0,5),(1,2)]
  | 59 => some [(4,4),(7,4),(8,4)]
  | _ => some [(0,0),(1,3),(6,3),(6,4)]
theorem root7Node152Domains1_fast_eq : root7Node152Domains1 = expandDomains root7Node152Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node152Domains1 v = expandDomains root7Node152Domains1Fast v from by decide) v
theorem root7Node152Step1Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root7Node152Domains0 root7Node152Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains0 root7Node152Domains1
    root7Node152Domains0Fast root7Node152Domains1Fast
    root7Node152Domains0_fast_eq root7Node152Domains1_fast_eq (by decide)
theorem root7Node152Step1_checked :
    checkReplacement table23 root7Node152Domains0 root7Node152Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node152Step1Chunk0_0_checked, root7Node152Step1Chunk0_1_checked, root7Node152Step1Chunk0_2_checked, root7Node152Step1Chunk0_3_checked, root7Node152Step1Chunk0_4_checked, root7Node152Step1Chunk0_5_checked, root7Node152Step1Chunk1_0_checked, root7Node152Step1Chunk1_1_checked, root7Node152Step1Chunk1_2_checked, root7Node152Step1Chunk1_3_checked, root7Node152Step1Chunk1_4_checked, root7Node152Step1Chunk1_5_checked, root7Node152Step1Chunk2_0_checked, root7Node152Step1Chunk2_1_checked, root7Node152Step1Chunk2_2_checked, root7Node152Step1Chunk2_3_checked, root7Node152Step1Chunk2_4_checked, root7Node152Step1Chunk2_5_checked, root7Node152Step1Chunk3_0_checked, root7Node152Step1Chunk3_1_checked, root7Node152Step1Chunk3_2_checked, root7Node152Step1Chunk3_3_checked, root7Node152Step1Chunk3_4_checked, root7Node152Step1Chunk3_5_checked, root7Node152Step1Chunk4_0_checked, root7Node152Step1Chunk4_1_checked, root7Node152Step1Chunk4_2_checked, root7Node152Step1Chunk4_3_checked, root7Node152Step1Chunk4_4_checked, root7Node152Step1Chunk4_5_checked, root7Node152Step1Chunk5_0_checked, root7Node152Step1Chunk5_1_checked, root7Node152Step1Chunk5_2_checked, root7Node152Step1Chunk5_3_checked, root7Node152Step1Chunk5_4_checked, root7Node152Step1Chunk5_5_checked, root7Node152Step1Chunk6_0_checked, root7Node152Step1Chunk6_1_checked, root7Node152Step1Chunk6_2_checked, root7Node152Step1Chunk6_3_checked, root7Node152Step1Chunk6_4_checked, root7Node152Step1Chunk6_5_checked, root7Node152Step1Chunk7_0_checked, root7Node152Step1Chunk7_1_checked, root7Node152Step1Chunk7_2_checked, root7Node152Step1Chunk7_3_checked, root7Node152Step1Chunk7_4_checked, root7Node152Step1Chunk7_5_checked, root7Node152Step1Chunk8_0_checked, root7Node152Step1Chunk8_1_checked, root7Node152Step1Chunk8_2_checked, root7Node152Step1Chunk8_3_checked, root7Node152Step1Chunk8_4_checked, root7Node152Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node152Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(4,5),(8,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(0,0),(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(0,2),(1,5)]
  | 19 => [(1,1),(6,1)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(3,4)]
  | 24 => [(6,3)]
  | 25 => [(7,2)]
  | 26 => [(4,5),(5,2),(5,5),(8,5)]
  | 27 => [(7,0),(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(7,0)]
  | 31 => [(2,3)]
  | 32 => [(0,2)]
  | 33 => [(1,1)]
  | 34 => [(4,1)]
  | 35 => [(4,4),(5,4),(7,2),(8,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(4,0)]
  | 42 => [(7,3)]
  | 43 => [(7,5)]
  | 44 => [(6,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(0,3)]
  | 48 => [(5,1)]
  | 49 => [(0,1)]
  | 50 => [(8,2)]
  | 51 => [(8,0)]
  | 52 => [(7,3)]
  | 53 => [(4,2)]
  | 54 => [(5,3)]
  | 55 => [(8,5)]
  | 56 => [(5,4),(8,4)]
  | 57 => [(6,4)]
  | 58 => [(1,2)]
  | 59 => [(7,4)]
  | _ => [(1,3),(6,3)]
def root7Node152Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(3,4)]
  | 24 => some [(6,3)]
  | 25 => some [(7,2)]
  | 26 => some [(4,5),(5,2),(5,5),(8,5)]
  | 27 => some [(7,0),(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,0)]
  | 31 => some [(2,3)]
  | 32 => some [(0,2)]
  | 33 => some [(1,1)]
  | 34 => some [(4,1)]
  | 35 => some [(4,4),(5,4),(7,2),(8,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(6,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(8,2)]
  | 51 => some [(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(6,4)]
  | 58 => some [(1,2)]
  | 59 => some [(7,4)]
  | _ => some [(1,3),(6,3)]
theorem root7Node152Domains2_fast_eq : root7Node152Domains2 = expandDomains root7Node152Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node152Domains2 v = expandDomains root7Node152Domains2Fast v from by decide) v
theorem root7Node152Step2Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root7Node152Domains1 root7Node152Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node152Domains1 root7Node152Domains2
    root7Node152Domains1Fast root7Node152Domains2Fast
    root7Node152Domains1_fast_eq root7Node152Domains2_fast_eq (by decide)
theorem root7Node152Step2_checked :
    checkReplacement table46 root7Node152Domains1 root7Node152Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node152Step2Chunk0_0_checked, root7Node152Step2Chunk0_1_checked, root7Node152Step2Chunk0_2_checked, root7Node152Step2Chunk0_3_checked, root7Node152Step2Chunk0_4_checked, root7Node152Step2Chunk0_5_checked, root7Node152Step2Chunk1_0_checked, root7Node152Step2Chunk1_1_checked, root7Node152Step2Chunk1_2_checked, root7Node152Step2Chunk1_3_checked, root7Node152Step2Chunk1_4_checked, root7Node152Step2Chunk1_5_checked, root7Node152Step2Chunk2_0_checked, root7Node152Step2Chunk2_1_checked, root7Node152Step2Chunk2_2_checked, root7Node152Step2Chunk2_3_checked, root7Node152Step2Chunk2_4_checked, root7Node152Step2Chunk2_5_checked, root7Node152Step2Chunk3_0_checked, root7Node152Step2Chunk3_1_checked, root7Node152Step2Chunk3_2_checked, root7Node152Step2Chunk3_3_checked, root7Node152Step2Chunk3_4_checked, root7Node152Step2Chunk3_5_checked, root7Node152Step2Chunk4_0_checked, root7Node152Step2Chunk4_1_checked, root7Node152Step2Chunk4_2_checked, root7Node152Step2Chunk4_3_checked, root7Node152Step2Chunk4_4_checked, root7Node152Step2Chunk4_5_checked, root7Node152Step2Chunk5_0_checked, root7Node152Step2Chunk5_1_checked, root7Node152Step2Chunk5_2_checked, root7Node152Step2Chunk5_3_checked, root7Node152Step2Chunk5_4_checked, root7Node152Step2Chunk5_5_checked, root7Node152Step2Chunk6_0_checked, root7Node152Step2Chunk6_1_checked, root7Node152Step2Chunk6_2_checked, root7Node152Step2Chunk6_3_checked, root7Node152Step2Chunk6_4_checked, root7Node152Step2Chunk6_5_checked, root7Node152Step2Chunk7_0_checked, root7Node152Step2Chunk7_1_checked, root7Node152Step2Chunk7_2_checked, root7Node152Step2Chunk7_3_checked, root7Node152Step2Chunk7_4_checked, root7Node152Step2Chunk7_5_checked, root7Node152Step2Chunk8_0_checked, root7Node152Step2Chunk8_1_checked, root7Node152Step2Chunk8_2_checked, root7Node152Step2Chunk8_3_checked, root7Node152Step2Chunk8_4_checked, root7Node152Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
