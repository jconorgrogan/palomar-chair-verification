module

public import SpectreFinite.RadiusFourRoot7Part40
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable16
public import SpectreFinite.RadiusFourTable23
public import SpectreFinite.RadiusFourTable29
public import SpectreFinite.RadiusFourTable36
public import SpectreFinite.RadiusFourTable40

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node122Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(7,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(8,0)]
  | 17 => [(7,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(1,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(8,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(7,5)]
  | 33 => [(0,3)]
  | 34 => [(4,1)]
  | 35 => [(0,4)]
  | 36 => [(3,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(6,3)]
  | 41 => [(2,2)]
  | 42 => [(3,3)]
  | 43 => [(2,3)]
  | 44 => [(0,2)]
  | 45 => [(1,1)]
  | 46 => [(4,1)]
  | 47 => [(0,2)]
  | 48 => [(1,1)]
  | 49 => [(0,1)]
  | 50 => [(1,2)]
  | 51 => [(4,0)]
  | 52 => [(7,3)]
  | 53 => [(5,2)]
  | 54 => [(5,0)]
  | 55 => [(4,5)]
  | 56 => [(5,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(8,4)]
  | _ => [(0,0)]
def root7Node122Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(1,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(4,1)]
  | 35 => some [(0,4)]
  | 36 => some [(3,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(6,3)]
  | 41 => some [(2,2)]
  | 42 => some [(3,3)]
  | 43 => some [(2,3)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(4,1)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(0,1)]
  | 50 => some [(1,2)]
  | 51 => some [(4,0)]
  | 52 => some [(7,3)]
  | 53 => some [(5,2)]
  | 54 => some [(5,0)]
  | 55 => some [(4,5)]
  | 56 => some [(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(0,0)]
theorem root7Node122Domains2_fast_eq : root7Node122Domains2 = expandDomains root7Node122Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node122Domains2 v = expandDomains root7Node122Domains2Fast v from by decide) v
theorem root7Node122Step2Chunk0_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_0⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk0_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_1⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk0_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_2⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk0_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_3⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk0_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_4⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk0_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_5⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk1_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_0⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk1_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_1⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk1_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_2⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk1_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_3⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk1_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_4⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk1_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_5⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk2_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_0⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk2_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_1⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk2_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_2⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk2_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_3⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk2_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_4⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk2_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_5⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk3_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_0⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk3_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_1⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk3_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_2⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk3_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_3⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk3_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_4⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk3_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_5⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk4_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_0⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk4_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_1⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk4_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_2⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk4_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_3⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk4_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_4⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk4_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_5⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk5_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_0⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk5_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_1⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk5_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_2⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk5_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_3⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk5_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_4⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk5_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_5⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk6_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_0⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk6_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_1⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk6_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_2⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk6_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_3⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk6_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_4⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk6_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_5⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk7_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_0⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk7_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_1⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk7_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_2⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk7_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_3⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk7_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_4⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk7_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_5⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk8_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_0⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk8_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_1⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk8_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_2⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk8_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_3⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk8_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_4⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2Chunk8_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_5⟩
      root7Node122Domains1 root7Node122Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node122Domains1 root7Node122Domains2
    root7Node122Domains1Fast root7Node122Domains2Fast
    root7Node122Domains1_fast_eq root7Node122Domains2_fast_eq (by decide)
theorem root7Node122Step2_checked :
    checkReplacement table16 root7Node122Domains1 root7Node122Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node122Step2Chunk0_0_checked, root7Node122Step2Chunk0_1_checked, root7Node122Step2Chunk0_2_checked, root7Node122Step2Chunk0_3_checked, root7Node122Step2Chunk0_4_checked, root7Node122Step2Chunk0_5_checked, root7Node122Step2Chunk1_0_checked, root7Node122Step2Chunk1_1_checked, root7Node122Step2Chunk1_2_checked, root7Node122Step2Chunk1_3_checked, root7Node122Step2Chunk1_4_checked, root7Node122Step2Chunk1_5_checked, root7Node122Step2Chunk2_0_checked, root7Node122Step2Chunk2_1_checked, root7Node122Step2Chunk2_2_checked, root7Node122Step2Chunk2_3_checked, root7Node122Step2Chunk2_4_checked, root7Node122Step2Chunk2_5_checked, root7Node122Step2Chunk3_0_checked, root7Node122Step2Chunk3_1_checked, root7Node122Step2Chunk3_2_checked, root7Node122Step2Chunk3_3_checked, root7Node122Step2Chunk3_4_checked, root7Node122Step2Chunk3_5_checked, root7Node122Step2Chunk4_0_checked, root7Node122Step2Chunk4_1_checked, root7Node122Step2Chunk4_2_checked, root7Node122Step2Chunk4_3_checked, root7Node122Step2Chunk4_4_checked, root7Node122Step2Chunk4_5_checked, root7Node122Step2Chunk5_0_checked, root7Node122Step2Chunk5_1_checked, root7Node122Step2Chunk5_2_checked, root7Node122Step2Chunk5_3_checked, root7Node122Step2Chunk5_4_checked, root7Node122Step2Chunk5_5_checked, root7Node122Step2Chunk6_0_checked, root7Node122Step2Chunk6_1_checked, root7Node122Step2Chunk6_2_checked, root7Node122Step2Chunk6_3_checked, root7Node122Step2Chunk6_4_checked, root7Node122Step2Chunk6_5_checked, root7Node122Step2Chunk7_0_checked, root7Node122Step2Chunk7_1_checked, root7Node122Step2Chunk7_2_checked, root7Node122Step2Chunk7_3_checked, root7Node122Step2Chunk7_4_checked, root7Node122Step2Chunk7_5_checked, root7Node122Step2Chunk8_0_checked, root7Node122Step2Chunk8_1_checked, root7Node122Step2Chunk8_2_checked, root7Node122Step2Chunk8_3_checked, root7Node122Step2Chunk8_4_checked, root7Node122Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root7Node122Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node122Domains2 (.output 60) = true := by decide
def root7Node123Domains0 : Domains 61 State := restrict root7Node119Domains1 26 (7,3)
def root7Node123Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(3,5),(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(4,1),(8,1)]
  | 35 => some [(0,4),(1,2),(6,2)]
  | 36 => some [(1,4),(3,4),(7,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(7,4)]
  | 40 => some [(0,5),(1,3),(6,3)]
  | 41 => some [(2,2),(2,4),(4,2)]
  | 42 => some [(1,3),(3,3),(5,3)]
  | 43 => some [(2,1),(2,3),(2,5),(4,1)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(7,1)]
  | 49 => some [(0,1),(1,4),(3,4),(6,5)]
  | 50 => some [(1,2),(3,2),(5,2),(7,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(5,2),(5,5),(8,2)]
  | 54 => some [(3,0),(5,0),(7,0)]
  | 55 => some [(2,3),(2,5),(4,5)]
  | 56 => some [(5,1),(5,4),(8,4)]
  | 57 => some [(0,1),(1,4),(6,4)]
  | 58 => some [(0,5),(1,2),(6,2)]
  | 59 => some [(4,4),(8,4)]
  | _ => some [(0,0),(6,4)]
theorem root7Node123Domains0_fast_eq : root7Node123Domains0 = expandDomains root7Node123Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node123Domains0 v = expandDomains root7Node123Domains0Fast v from by decide) v
def root7Node123Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(7,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(8,0)]
  | 17 => [(7,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(7,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(8,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(7,5)]
  | 33 => [(0,3)]
  | 34 => [(4,1),(8,1)]
  | 35 => [(1,2),(6,2)]
  | 36 => [(7,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(1,3),(6,3)]
  | 41 => [(2,2),(2,4),(4,2)]
  | 42 => [(1,3),(3,3),(5,3)]
  | 43 => [(2,1),(4,1)]
  | 44 => [(0,2)]
  | 45 => [(1,1)]
  | 46 => [(4,1),(8,1)]
  | 47 => [(0,2),(6,5)]
  | 48 => [(0,4),(1,1),(7,1)]
  | 49 => [(0,1),(1,4),(3,4),(6,5)]
  | 50 => [(3,2),(5,2)]
  | 51 => [(4,0),(8,0)]
  | 52 => [(7,3),(8,3)]
  | 53 => [(5,2),(5,5)]
  | 54 => [(3,0),(5,0),(7,0)]
  | 55 => [(2,3),(2,5),(4,5)]
  | 56 => [(5,1),(5,4),(8,4)]
  | 57 => [(0,1),(1,4),(6,4)]
  | 58 => [(0,5),(1,2),(6,2)]
  | 59 => [(4,4),(8,4)]
  | _ => [(0,0),(6,4)]
def root7Node123Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(4,1),(8,1)]
  | 35 => some [(1,2),(6,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3),(6,3)]
  | 41 => some [(2,2),(2,4),(4,2)]
  | 42 => some [(1,3),(3,3),(5,3)]
  | 43 => some [(2,1),(4,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(4,1),(8,1)]
  | 47 => some [(0,2),(6,5)]
  | 48 => some [(0,4),(1,1),(7,1)]
  | 49 => some [(0,1),(1,4),(3,4),(6,5)]
  | 50 => some [(3,2),(5,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(5,2),(5,5)]
  | 54 => some [(3,0),(5,0),(7,0)]
  | 55 => some [(2,3),(2,5),(4,5)]
  | 56 => some [(5,1),(5,4),(8,4)]
  | 57 => some [(0,1),(1,4),(6,4)]
  | 58 => some [(0,5),(1,2),(6,2)]
  | 59 => some [(4,4),(8,4)]
  | _ => some [(0,0),(6,4)]
theorem root7Node123Domains1_fast_eq : root7Node123Domains1 = expandDomains root7Node123Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node123Domains1 v = expandDomains root7Node123Domains1Fast v from by decide) v
theorem root7Node123Step1Chunk0_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_0⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk0_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_1⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk0_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_2⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk0_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_3⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk0_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_4⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk0_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_5⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk1_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_0⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk1_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_1⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk1_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_2⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk1_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_3⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk1_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_4⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk1_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_5⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk2_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_0⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk2_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_1⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk2_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_2⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk2_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_3⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk2_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_4⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk2_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_5⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk3_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_0⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk3_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_1⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk3_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_2⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk3_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_3⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk3_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_4⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk3_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_5⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk4_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_0⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk4_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_1⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk4_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_2⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk4_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_3⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk4_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_4⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk4_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_5⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk5_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_0⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk5_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_1⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk5_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_2⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk5_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_3⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk5_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_4⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk5_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_5⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk6_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_0⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk6_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_1⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk6_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_2⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk6_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_3⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk6_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_4⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk6_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_5⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk7_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_0⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk7_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_1⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk7_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_2⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk7_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_3⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk7_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_4⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk7_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_5⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk8_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_0⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk8_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_1⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk8_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_2⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk8_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_3⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk8_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_4⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk8_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_5⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1_checked :
    checkReplacement table29 root7Node123Domains0 root7Node123Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node123Step1Chunk0_0_checked, root7Node123Step1Chunk0_1_checked, root7Node123Step1Chunk0_2_checked, root7Node123Step1Chunk0_3_checked, root7Node123Step1Chunk0_4_checked, root7Node123Step1Chunk0_5_checked, root7Node123Step1Chunk1_0_checked, root7Node123Step1Chunk1_1_checked, root7Node123Step1Chunk1_2_checked, root7Node123Step1Chunk1_3_checked, root7Node123Step1Chunk1_4_checked, root7Node123Step1Chunk1_5_checked, root7Node123Step1Chunk2_0_checked, root7Node123Step1Chunk2_1_checked, root7Node123Step1Chunk2_2_checked, root7Node123Step1Chunk2_3_checked, root7Node123Step1Chunk2_4_checked, root7Node123Step1Chunk2_5_checked, root7Node123Step1Chunk3_0_checked, root7Node123Step1Chunk3_1_checked, root7Node123Step1Chunk3_2_checked, root7Node123Step1Chunk3_3_checked, root7Node123Step1Chunk3_4_checked, root7Node123Step1Chunk3_5_checked, root7Node123Step1Chunk4_0_checked, root7Node123Step1Chunk4_1_checked, root7Node123Step1Chunk4_2_checked, root7Node123Step1Chunk4_3_checked, root7Node123Step1Chunk4_4_checked, root7Node123Step1Chunk4_5_checked, root7Node123Step1Chunk5_0_checked, root7Node123Step1Chunk5_1_checked, root7Node123Step1Chunk5_2_checked, root7Node123Step1Chunk5_3_checked, root7Node123Step1Chunk5_4_checked, root7Node123Step1Chunk5_5_checked, root7Node123Step1Chunk6_0_checked, root7Node123Step1Chunk6_1_checked, root7Node123Step1Chunk6_2_checked, root7Node123Step1Chunk6_3_checked, root7Node123Step1Chunk6_4_checked, root7Node123Step1Chunk6_5_checked, root7Node123Step1Chunk7_0_checked, root7Node123Step1Chunk7_1_checked, root7Node123Step1Chunk7_2_checked, root7Node123Step1Chunk7_3_checked, root7Node123Step1Chunk7_4_checked, root7Node123Step1Chunk7_5_checked, root7Node123Step1Chunk8_0_checked, root7Node123Step1Chunk8_1_checked, root7Node123Step1Chunk8_2_checked, root7Node123Step1Chunk8_3_checked, root7Node123Step1Chunk8_4_checked, root7Node123Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node123Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(7,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(8,0)]
  | 17 => [(7,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(7,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(8,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(7,5)]
  | 33 => [(0,3)]
  | 34 => [(4,1),(8,1)]
  | 35 => [(1,2),(6,2)]
  | 36 => [(7,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(1,3),(6,3)]
  | 41 => [(2,2),(4,2)]
  | 42 => [(3,3),(5,3)]
  | 43 => [(2,1),(4,1)]
  | 44 => [(0,2)]
  | 45 => [(1,1)]
  | 46 => [(4,1),(8,1)]
  | 47 => [(0,2),(6,5)]
  | 48 => [(0,4),(1,1)]
  | 49 => [(0,1),(1,4),(3,4)]
  | 50 => [(3,2),(5,2)]
  | 51 => [(4,0),(8,0)]
  | 52 => [(7,3),(8,3)]
  | 53 => [(5,2),(5,5)]
  | 54 => [(3,0),(5,0),(7,0)]
  | 55 => [(2,3),(2,5),(4,5)]
  | 56 => [(5,1),(5,4),(8,4)]
  | 57 => [(0,1),(1,4),(6,4)]
  | 58 => [(0,5),(1,2),(6,2)]
  | 59 => [(4,4),(8,4)]
  | _ => [(0,0),(6,4)]
def root7Node123Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(4,1),(8,1)]
  | 35 => some [(1,2),(6,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3),(6,3)]
  | 41 => some [(2,2),(4,2)]
  | 42 => some [(3,3),(5,3)]
  | 43 => some [(2,1),(4,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(4,1),(8,1)]
  | 47 => some [(0,2),(6,5)]
  | 48 => some [(0,4),(1,1)]
  | 49 => some [(0,1),(1,4),(3,4)]
  | 50 => some [(3,2),(5,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(5,2),(5,5)]
  | 54 => some [(3,0),(5,0),(7,0)]
  | 55 => some [(2,3),(2,5),(4,5)]
  | 56 => some [(5,1),(5,4),(8,4)]
  | 57 => some [(0,1),(1,4),(6,4)]
  | 58 => some [(0,5),(1,2),(6,2)]
  | 59 => some [(4,4),(8,4)]
  | _ => some [(0,0),(6,4)]
theorem root7Node123Domains2_fast_eq : root7Node123Domains2 = expandDomains root7Node123Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node123Domains2 v = expandDomains root7Node123Domains2Fast v from by decide) v
theorem root7Node123Step2Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root7Node123Domains1 root7Node123Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains1 root7Node123Domains2
    root7Node123Domains1Fast root7Node123Domains2Fast
    root7Node123Domains1_fast_eq root7Node123Domains2_fast_eq (by decide)
theorem root7Node123Step2_checked :
    checkReplacement table23 root7Node123Domains1 root7Node123Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node123Step2Chunk0_0_checked, root7Node123Step2Chunk0_1_checked, root7Node123Step2Chunk0_2_checked, root7Node123Step2Chunk0_3_checked, root7Node123Step2Chunk0_4_checked, root7Node123Step2Chunk0_5_checked, root7Node123Step2Chunk1_0_checked, root7Node123Step2Chunk1_1_checked, root7Node123Step2Chunk1_2_checked, root7Node123Step2Chunk1_3_checked, root7Node123Step2Chunk1_4_checked, root7Node123Step2Chunk1_5_checked, root7Node123Step2Chunk2_0_checked, root7Node123Step2Chunk2_1_checked, root7Node123Step2Chunk2_2_checked, root7Node123Step2Chunk2_3_checked, root7Node123Step2Chunk2_4_checked, root7Node123Step2Chunk2_5_checked, root7Node123Step2Chunk3_0_checked, root7Node123Step2Chunk3_1_checked, root7Node123Step2Chunk3_2_checked, root7Node123Step2Chunk3_3_checked, root7Node123Step2Chunk3_4_checked, root7Node123Step2Chunk3_5_checked, root7Node123Step2Chunk4_0_checked, root7Node123Step2Chunk4_1_checked, root7Node123Step2Chunk4_2_checked, root7Node123Step2Chunk4_3_checked, root7Node123Step2Chunk4_4_checked, root7Node123Step2Chunk4_5_checked, root7Node123Step2Chunk5_0_checked, root7Node123Step2Chunk5_1_checked, root7Node123Step2Chunk5_2_checked, root7Node123Step2Chunk5_3_checked, root7Node123Step2Chunk5_4_checked, root7Node123Step2Chunk5_5_checked, root7Node123Step2Chunk6_0_checked, root7Node123Step2Chunk6_1_checked, root7Node123Step2Chunk6_2_checked, root7Node123Step2Chunk6_3_checked, root7Node123Step2Chunk6_4_checked, root7Node123Step2Chunk6_5_checked, root7Node123Step2Chunk7_0_checked, root7Node123Step2Chunk7_1_checked, root7Node123Step2Chunk7_2_checked, root7Node123Step2Chunk7_3_checked, root7Node123Step2Chunk7_4_checked, root7Node123Step2Chunk7_5_checked, root7Node123Step2Chunk8_0_checked, root7Node123Step2Chunk8_1_checked, root7Node123Step2Chunk8_2_checked, root7Node123Step2Chunk8_3_checked, root7Node123Step2Chunk8_4_checked, root7Node123Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node124Domains0 : Domains 61 State := restrict root7Node123Domains2 34 (4,1)
def root7Node124Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(4,1)]
  | 35 => some [(1,2),(6,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3),(6,3)]
  | 41 => some [(2,2),(4,2)]
  | 42 => some [(3,3),(5,3)]
  | 43 => some [(2,1),(4,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(4,1),(8,1)]
  | 47 => some [(0,2),(6,5)]
  | 48 => some [(0,4),(1,1)]
  | 49 => some [(0,1),(1,4),(3,4)]
  | 50 => some [(3,2),(5,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(5,2),(5,5)]
  | 54 => some [(3,0),(5,0),(7,0)]
  | 55 => some [(2,3),(2,5),(4,5)]
  | 56 => some [(5,1),(5,4),(8,4)]
  | 57 => some [(0,1),(1,4),(6,4)]
  | 58 => some [(0,5),(1,2),(6,2)]
  | 59 => some [(4,4),(8,4)]
  | _ => some [(0,0),(6,4)]
theorem root7Node124Domains0_fast_eq : root7Node124Domains0 = expandDomains root7Node124Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node124Domains0 v = expandDomains root7Node124Domains0Fast v from by decide) v
def root7Node124Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(7,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(8,0)]
  | 17 => [(7,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(7,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(8,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(7,5)]
  | 33 => [(0,3)]
  | 34 => [(4,1)]
  | 35 => [(1,2),(6,2)]
  | 36 => [(7,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(6,3)]
  | 41 => [(2,2)]
  | 42 => [(3,3)]
  | 43 => [(2,1),(4,1)]
  | 44 => [(0,2)]
  | 45 => [(1,1)]
  | 46 => [(4,1)]
  | 47 => [(0,2)]
  | 48 => [(1,1)]
  | 49 => [(0,1)]
  | 50 => [(3,2),(5,2)]
  | 51 => [(4,0),(8,0)]
  | 52 => [(7,3)]
  | 53 => [(5,2)]
  | 54 => [(5,0)]
  | 55 => [(4,5)]
  | 56 => [(5,1),(5,4),(8,4)]
  | 57 => [(0,1),(1,4),(6,4)]
  | 58 => [(1,2),(6,2)]
  | 59 => [(8,4)]
  | _ => [(0,0)]
def root7Node124Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(4,1)]
  | 35 => some [(1,2),(6,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(6,3)]
  | 41 => some [(2,2)]
  | 42 => some [(3,3)]
  | 43 => some [(2,1),(4,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(4,1)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(0,1)]
  | 50 => some [(3,2),(5,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(5,2)]
  | 54 => some [(5,0)]
  | 55 => some [(4,5)]
  | 56 => some [(5,1),(5,4),(8,4)]
  | 57 => some [(0,1),(1,4),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(0,0)]
theorem root7Node124Domains1_fast_eq : root7Node124Domains1 = expandDomains root7Node124Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node124Domains1 v = expandDomains root7Node124Domains1Fast v from by decide) v
theorem root7Node124Step1Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1_checked :
    checkReplacement table40 root7Node124Domains0 root7Node124Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node124Step1Chunk0_0_checked, root7Node124Step1Chunk0_1_checked, root7Node124Step1Chunk0_2_checked, root7Node124Step1Chunk0_3_checked, root7Node124Step1Chunk0_4_checked, root7Node124Step1Chunk0_5_checked, root7Node124Step1Chunk1_0_checked, root7Node124Step1Chunk1_1_checked, root7Node124Step1Chunk1_2_checked, root7Node124Step1Chunk1_3_checked, root7Node124Step1Chunk1_4_checked, root7Node124Step1Chunk1_5_checked, root7Node124Step1Chunk2_0_checked, root7Node124Step1Chunk2_1_checked, root7Node124Step1Chunk2_2_checked, root7Node124Step1Chunk2_3_checked, root7Node124Step1Chunk2_4_checked, root7Node124Step1Chunk2_5_checked, root7Node124Step1Chunk3_0_checked, root7Node124Step1Chunk3_1_checked, root7Node124Step1Chunk3_2_checked, root7Node124Step1Chunk3_3_checked, root7Node124Step1Chunk3_4_checked, root7Node124Step1Chunk3_5_checked, root7Node124Step1Chunk4_0_checked, root7Node124Step1Chunk4_1_checked, root7Node124Step1Chunk4_2_checked, root7Node124Step1Chunk4_3_checked, root7Node124Step1Chunk4_4_checked, root7Node124Step1Chunk4_5_checked, root7Node124Step1Chunk5_0_checked, root7Node124Step1Chunk5_1_checked, root7Node124Step1Chunk5_2_checked, root7Node124Step1Chunk5_3_checked, root7Node124Step1Chunk5_4_checked, root7Node124Step1Chunk5_5_checked, root7Node124Step1Chunk6_0_checked, root7Node124Step1Chunk6_1_checked, root7Node124Step1Chunk6_2_checked, root7Node124Step1Chunk6_3_checked, root7Node124Step1Chunk6_4_checked, root7Node124Step1Chunk6_5_checked, root7Node124Step1Chunk7_0_checked, root7Node124Step1Chunk7_1_checked, root7Node124Step1Chunk7_2_checked, root7Node124Step1Chunk7_3_checked, root7Node124Step1Chunk7_4_checked, root7Node124Step1Chunk7_5_checked, root7Node124Step1Chunk8_0_checked, root7Node124Step1Chunk8_1_checked, root7Node124Step1Chunk8_2_checked, root7Node124Step1Chunk8_3_checked, root7Node124Step1Chunk8_4_checked, root7Node124Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node124Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(7,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(8,0)]
  | 17 => [(7,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(7,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(8,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(7,5)]
  | 33 => [(0,3)]
  | 34 => [(4,1)]
  | 35 => [(1,2),(6,2)]
  | 36 => [(7,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(6,3)]
  | 41 => [(2,2)]
  | 42 => [(3,3)]
  | 43 => [(2,1),(4,1)]
  | 44 => [(0,2)]
  | 45 => [(1,1)]
  | 46 => [(4,1)]
  | 47 => [(0,2)]
  | 48 => [(1,1)]
  | 49 => [(0,1)]
  | 50 => [(3,2),(5,2)]
  | 51 => [(4,0),(8,0)]
  | 52 => [(7,3)]
  | 53 => [(5,2)]
  | 54 => [(5,0)]
  | 55 => [(4,5)]
  | 56 => [(5,1),(5,4),(8,4)]
  | 57 => [(0,1),(6,4)]
  | 58 => [(1,2),(6,2)]
  | 59 => [(8,4)]
  | _ => [(0,0)]
def root7Node124Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(4,1)]
  | 35 => some [(1,2),(6,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(6,3)]
  | 41 => some [(2,2)]
  | 42 => some [(3,3)]
  | 43 => some [(2,1),(4,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(4,1)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(0,1)]
  | 50 => some [(3,2),(5,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(5,2)]
  | 54 => some [(5,0)]
  | 55 => some [(4,5)]
  | 56 => some [(5,1),(5,4),(8,4)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(0,0)]
theorem root7Node124Domains2_fast_eq : root7Node124Domains2 = expandDomains root7Node124Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node124Domains2 v = expandDomains root7Node124Domains2Fast v from by decide) v
theorem root7Node124Step2Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root7Node124Domains1 root7Node124Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains1 root7Node124Domains2
    root7Node124Domains1Fast root7Node124Domains2Fast
    root7Node124Domains1_fast_eq root7Node124Domains2_fast_eq (by decide)
theorem root7Node124Step2_checked :
    checkReplacement table36 root7Node124Domains1 root7Node124Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node124Step2Chunk0_0_checked, root7Node124Step2Chunk0_1_checked, root7Node124Step2Chunk0_2_checked, root7Node124Step2Chunk0_3_checked, root7Node124Step2Chunk0_4_checked, root7Node124Step2Chunk0_5_checked, root7Node124Step2Chunk1_0_checked, root7Node124Step2Chunk1_1_checked, root7Node124Step2Chunk1_2_checked, root7Node124Step2Chunk1_3_checked, root7Node124Step2Chunk1_4_checked, root7Node124Step2Chunk1_5_checked, root7Node124Step2Chunk2_0_checked, root7Node124Step2Chunk2_1_checked, root7Node124Step2Chunk2_2_checked, root7Node124Step2Chunk2_3_checked, root7Node124Step2Chunk2_4_checked, root7Node124Step2Chunk2_5_checked, root7Node124Step2Chunk3_0_checked, root7Node124Step2Chunk3_1_checked, root7Node124Step2Chunk3_2_checked, root7Node124Step2Chunk3_3_checked, root7Node124Step2Chunk3_4_checked, root7Node124Step2Chunk3_5_checked, root7Node124Step2Chunk4_0_checked, root7Node124Step2Chunk4_1_checked, root7Node124Step2Chunk4_2_checked, root7Node124Step2Chunk4_3_checked, root7Node124Step2Chunk4_4_checked, root7Node124Step2Chunk4_5_checked, root7Node124Step2Chunk5_0_checked, root7Node124Step2Chunk5_1_checked, root7Node124Step2Chunk5_2_checked, root7Node124Step2Chunk5_3_checked, root7Node124Step2Chunk5_4_checked, root7Node124Step2Chunk5_5_checked, root7Node124Step2Chunk6_0_checked, root7Node124Step2Chunk6_1_checked, root7Node124Step2Chunk6_2_checked, root7Node124Step2Chunk6_3_checked, root7Node124Step2Chunk6_4_checked, root7Node124Step2Chunk6_5_checked, root7Node124Step2Chunk7_0_checked, root7Node124Step2Chunk7_1_checked, root7Node124Step2Chunk7_2_checked, root7Node124Step2Chunk7_3_checked, root7Node124Step2Chunk7_4_checked, root7Node124Step2Chunk7_5_checked, root7Node124Step2Chunk8_0_checked, root7Node124Step2Chunk8_1_checked, root7Node124Step2Chunk8_2_checked, root7Node124Step2Chunk8_3_checked, root7Node124Step2Chunk8_4_checked, root7Node124Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
