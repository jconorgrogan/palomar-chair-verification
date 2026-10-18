module

public import SpectreFinite.RadiusFourRoot3Part2
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable35
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root3Node3Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(8,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(5,5)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(1,4)]
  | 24 => [(0,5)]
  | 25 => [(4,4)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(3,0)]
  | 31 => [(2,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(7,5)]
  | 35 => [(5,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0)]
  | 42 => [(7,3)]
  | 43 => [(7,5)]
  | 44 => [(6,0)]
  | 45 => [(7,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1)]
  | 49 => [(0,1)]
  | 50 => [(8,2)]
  | 51 => [(5,0)]
  | 52 => [(4,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(8,5)]
  | 56 => [(5,4)]
  | 57 => [(0,0)]
  | 58 => [(7,2)]
  | 59 => [(7,4)]
  | _ => [(6,3)]
def root3Node3Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(1,4)]
  | 24 => some [(0,5)]
  | 25 => some [(4,4)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(3,0)]
  | 31 => some [(2,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(5,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(6,0)]
  | 45 => some [(7,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(8,2)]
  | 51 => some [(5,0)]
  | 52 => some [(4,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,4)]
  | 57 => some [(0,0)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root3Node3Domains2_fast_eq : root3Node3Domains2 = expandDomains root3Node3Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root3Node3Domains2 v = expandDomains root3Node3Domains2Fast v from by decide) v
theorem root3Node3Step2Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root3Node3Domains1 root3Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node3Domains1 root3Node3Domains2
    root3Node3Domains1Fast root3Node3Domains2Fast
    root3Node3Domains1_fast_eq root3Node3Domains2_fast_eq (by decide)
theorem root3Node3Step2_checked :
    checkReplacement table46 root3Node3Domains1 root3Node3Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root3Node3Step2Chunk0_0_checked, root3Node3Step2Chunk0_1_checked, root3Node3Step2Chunk0_2_checked, root3Node3Step2Chunk0_3_checked, root3Node3Step2Chunk0_4_checked, root3Node3Step2Chunk0_5_checked, root3Node3Step2Chunk1_0_checked, root3Node3Step2Chunk1_1_checked, root3Node3Step2Chunk1_2_checked, root3Node3Step2Chunk1_3_checked, root3Node3Step2Chunk1_4_checked, root3Node3Step2Chunk1_5_checked, root3Node3Step2Chunk2_0_checked, root3Node3Step2Chunk2_1_checked, root3Node3Step2Chunk2_2_checked, root3Node3Step2Chunk2_3_checked, root3Node3Step2Chunk2_4_checked, root3Node3Step2Chunk2_5_checked, root3Node3Step2Chunk3_0_checked, root3Node3Step2Chunk3_1_checked, root3Node3Step2Chunk3_2_checked, root3Node3Step2Chunk3_3_checked, root3Node3Step2Chunk3_4_checked, root3Node3Step2Chunk3_5_checked, root3Node3Step2Chunk4_0_checked, root3Node3Step2Chunk4_1_checked, root3Node3Step2Chunk4_2_checked, root3Node3Step2Chunk4_3_checked, root3Node3Step2Chunk4_4_checked, root3Node3Step2Chunk4_5_checked, root3Node3Step2Chunk5_0_checked, root3Node3Step2Chunk5_1_checked, root3Node3Step2Chunk5_2_checked, root3Node3Step2Chunk5_3_checked, root3Node3Step2Chunk5_4_checked, root3Node3Step2Chunk5_5_checked, root3Node3Step2Chunk6_0_checked, root3Node3Step2Chunk6_1_checked, root3Node3Step2Chunk6_2_checked, root3Node3Step2Chunk6_3_checked, root3Node3Step2Chunk6_4_checked, root3Node3Step2Chunk6_5_checked, root3Node3Step2Chunk7_0_checked, root3Node3Step2Chunk7_1_checked, root3Node3Step2Chunk7_2_checked, root3Node3Step2Chunk7_3_checked, root3Node3Step2Chunk7_4_checked, root3Node3Step2Chunk7_5_checked, root3Node3Step2Chunk8_0_checked, root3Node3Step2Chunk8_1_checked, root3Node3Step2Chunk8_2_checked, root3Node3Step2Chunk8_3_checked, root3Node3Step2Chunk8_4_checked, root3Node3Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root3Node3Leaf_checked :
    checkCover 1 constraints root3Outputs root3Node3Domains2 (.output 1) = true := by decide
def root3Node4Domains0 : Domains 61 State := restrict root3Node2Domains1 35 (8,4)
def root3Node4Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(1,4)]
  | 24 => some [(0,5)]
  | 25 => some [(4,4)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(3,0)]
  | 31 => some [(2,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(8,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(6,0)]
  | 45 => some [(7,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(8,2)]
  | 51 => some [(5,0)]
  | 52 => some [(4,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(0,0)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(1,3),(6,3)]
theorem root3Node4Domains0_fast_eq : root3Node4Domains0 = expandDomains root3Node4Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root3Node4Domains0 v = expandDomains root3Node4Domains0Fast v from by decide) v
def root3Node4Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(8,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(5,5)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(1,4)]
  | 24 => [(0,5)]
  | 25 => [(4,4)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(3,0)]
  | 31 => [(2,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(7,5)]
  | 35 => [(8,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0)]
  | 42 => [(7,3)]
  | 43 => [(7,5)]
  | 44 => [(6,0)]
  | 45 => [(7,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1)]
  | 49 => [(0,1)]
  | 50 => [(8,2)]
  | 51 => [(5,0)]
  | 52 => [(4,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(8,5)]
  | 56 => [(8,4)]
  | 57 => [(0,0)]
  | 58 => [(7,2)]
  | 59 => [(7,4)]
  | _ => [(1,3),(6,3)]
def root3Node4Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(1,4)]
  | 24 => some [(0,5)]
  | 25 => some [(4,4)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(3,0)]
  | 31 => some [(2,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(8,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(6,0)]
  | 45 => some [(7,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(8,2)]
  | 51 => some [(5,0)]
  | 52 => some [(4,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => some [(8,4)]
  | 57 => some [(0,0)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(1,3),(6,3)]
theorem root3Node4Domains1_fast_eq : root3Node4Domains1 = expandDomains root3Node4Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root3Node4Domains1 v = expandDomains root3Node4Domains1Fast v from by decide) v
theorem root3Node4Step1Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root3Node4Domains0 root3Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains0 root3Node4Domains1
    root3Node4Domains0Fast root3Node4Domains1Fast
    root3Node4Domains0_fast_eq root3Node4Domains1_fast_eq (by decide)
theorem root3Node4Step1_checked :
    checkReplacement table35 root3Node4Domains0 root3Node4Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root3Node4Step1Chunk0_0_checked, root3Node4Step1Chunk0_1_checked, root3Node4Step1Chunk0_2_checked, root3Node4Step1Chunk0_3_checked, root3Node4Step1Chunk0_4_checked, root3Node4Step1Chunk0_5_checked, root3Node4Step1Chunk1_0_checked, root3Node4Step1Chunk1_1_checked, root3Node4Step1Chunk1_2_checked, root3Node4Step1Chunk1_3_checked, root3Node4Step1Chunk1_4_checked, root3Node4Step1Chunk1_5_checked, root3Node4Step1Chunk2_0_checked, root3Node4Step1Chunk2_1_checked, root3Node4Step1Chunk2_2_checked, root3Node4Step1Chunk2_3_checked, root3Node4Step1Chunk2_4_checked, root3Node4Step1Chunk2_5_checked, root3Node4Step1Chunk3_0_checked, root3Node4Step1Chunk3_1_checked, root3Node4Step1Chunk3_2_checked, root3Node4Step1Chunk3_3_checked, root3Node4Step1Chunk3_4_checked, root3Node4Step1Chunk3_5_checked, root3Node4Step1Chunk4_0_checked, root3Node4Step1Chunk4_1_checked, root3Node4Step1Chunk4_2_checked, root3Node4Step1Chunk4_3_checked, root3Node4Step1Chunk4_4_checked, root3Node4Step1Chunk4_5_checked, root3Node4Step1Chunk5_0_checked, root3Node4Step1Chunk5_1_checked, root3Node4Step1Chunk5_2_checked, root3Node4Step1Chunk5_3_checked, root3Node4Step1Chunk5_4_checked, root3Node4Step1Chunk5_5_checked, root3Node4Step1Chunk6_0_checked, root3Node4Step1Chunk6_1_checked, root3Node4Step1Chunk6_2_checked, root3Node4Step1Chunk6_3_checked, root3Node4Step1Chunk6_4_checked, root3Node4Step1Chunk6_5_checked, root3Node4Step1Chunk7_0_checked, root3Node4Step1Chunk7_1_checked, root3Node4Step1Chunk7_2_checked, root3Node4Step1Chunk7_3_checked, root3Node4Step1Chunk7_4_checked, root3Node4Step1Chunk7_5_checked, root3Node4Step1Chunk8_0_checked, root3Node4Step1Chunk8_1_checked, root3Node4Step1Chunk8_2_checked, root3Node4Step1Chunk8_3_checked, root3Node4Step1Chunk8_4_checked, root3Node4Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root3Node4Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(8,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(5,5)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(1,4)]
  | 24 => [(0,5)]
  | 25 => [(4,4)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(3,0)]
  | 31 => [(2,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(7,5)]
  | 35 => [(8,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0)]
  | 42 => [(7,3)]
  | 43 => [(7,5)]
  | 44 => [(6,0)]
  | 45 => [(7,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1)]
  | 49 => [(0,1)]
  | 50 => [(8,2)]
  | 51 => [(5,0)]
  | 52 => [(4,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(8,5)]
  | 56 => [(8,4)]
  | 57 => [(0,0)]
  | 58 => [(7,2)]
  | 59 => [(7,4)]
  | _ => [(1,3)]
def root3Node4Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(1,4)]
  | 24 => some [(0,5)]
  | 25 => some [(4,4)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(3,0)]
  | 31 => some [(2,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(8,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(6,0)]
  | 45 => some [(7,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(8,2)]
  | 51 => some [(5,0)]
  | 52 => some [(4,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => some [(8,4)]
  | 57 => some [(0,0)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(1,3)]
theorem root3Node4Domains2_fast_eq : root3Node4Domains2 = expandDomains root3Node4Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root3Node4Domains2 v = expandDomains root3Node4Domains2Fast v from by decide) v
theorem root3Node4Step2Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root3Node4Domains1 root3Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root3Node4Domains1 root3Node4Domains2
    root3Node4Domains1Fast root3Node4Domains2Fast
    root3Node4Domains1_fast_eq root3Node4Domains2_fast_eq (by decide)
theorem root3Node4Step2_checked :
    checkReplacement table46 root3Node4Domains1 root3Node4Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root3Node4Step2Chunk0_0_checked, root3Node4Step2Chunk0_1_checked, root3Node4Step2Chunk0_2_checked, root3Node4Step2Chunk0_3_checked, root3Node4Step2Chunk0_4_checked, root3Node4Step2Chunk0_5_checked, root3Node4Step2Chunk1_0_checked, root3Node4Step2Chunk1_1_checked, root3Node4Step2Chunk1_2_checked, root3Node4Step2Chunk1_3_checked, root3Node4Step2Chunk1_4_checked, root3Node4Step2Chunk1_5_checked, root3Node4Step2Chunk2_0_checked, root3Node4Step2Chunk2_1_checked, root3Node4Step2Chunk2_2_checked, root3Node4Step2Chunk2_3_checked, root3Node4Step2Chunk2_4_checked, root3Node4Step2Chunk2_5_checked, root3Node4Step2Chunk3_0_checked, root3Node4Step2Chunk3_1_checked, root3Node4Step2Chunk3_2_checked, root3Node4Step2Chunk3_3_checked, root3Node4Step2Chunk3_4_checked, root3Node4Step2Chunk3_5_checked, root3Node4Step2Chunk4_0_checked, root3Node4Step2Chunk4_1_checked, root3Node4Step2Chunk4_2_checked, root3Node4Step2Chunk4_3_checked, root3Node4Step2Chunk4_4_checked, root3Node4Step2Chunk4_5_checked, root3Node4Step2Chunk5_0_checked, root3Node4Step2Chunk5_1_checked, root3Node4Step2Chunk5_2_checked, root3Node4Step2Chunk5_3_checked, root3Node4Step2Chunk5_4_checked, root3Node4Step2Chunk5_5_checked, root3Node4Step2Chunk6_0_checked, root3Node4Step2Chunk6_1_checked, root3Node4Step2Chunk6_2_checked, root3Node4Step2Chunk6_3_checked, root3Node4Step2Chunk6_4_checked, root3Node4Step2Chunk6_5_checked, root3Node4Step2Chunk7_0_checked, root3Node4Step2Chunk7_1_checked, root3Node4Step2Chunk7_2_checked, root3Node4Step2Chunk7_3_checked, root3Node4Step2Chunk7_4_checked, root3Node4Step2Chunk7_5_checked, root3Node4Step2Chunk8_0_checked, root3Node4Step2Chunk8_1_checked, root3Node4Step2Chunk8_2_checked, root3Node4Step2Chunk8_3_checked, root3Node4Step2Chunk8_4_checked, root3Node4Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root3Node4Leaf_checked :
    checkCover 1 constraints root3Outputs root3Node4Domains2 (.output 2) = true := by decide
end SpectreFinite.HexSearch.RadiusFour
