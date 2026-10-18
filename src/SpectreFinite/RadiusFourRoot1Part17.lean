module

public import SpectreFinite.RadiusFourRoot1Part16
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable22
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node47Domains2 (v : Fin 61) : List State :=
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
  | 48 => [(6,2)]
  | 49 => [(7,4)]
  | 50 => [(5,2)]
  | 51 => [(8,0)]
  | 52 => [(8,3)]
  | 53 => [(5,5)]
  | 54 => [(1,0)]
  | 55 => [(2,1)]
  | 56 => [(8,4)]
  | 57 => [(1,4)]
  | 58 => [(0,5)]
  | 59 => [(4,4)]
  | _ => [(0,0)]
def root1Node47Domains2Fast (v : Fin 61) : Option (List State) :=
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
  | 48 => some [(6,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,2)]
  | 51 => some [(8,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5)]
  | 54 => some [(1,0)]
  | 55 => some [(2,1)]
  | 56 => some [(8,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(4,4)]
  | _ => some [(0,0)]
theorem root1Node47Domains2_fast_eq : root1Node47Domains2 = expandDomains root1Node47Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node47Domains2 v = expandDomains root1Node47Domains2Fast v from by decide) v
theorem root1Node47Step2Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root1Node47Domains1 root1Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node47Domains1 root1Node47Domains2
    root1Node47Domains1Fast root1Node47Domains2Fast
    root1Node47Domains1_fast_eq root1Node47Domains2_fast_eq (by decide)
theorem root1Node47Step2_checked :
    checkReplacement table46 root1Node47Domains1 root1Node47Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node47Step2Chunk0_0_checked, root1Node47Step2Chunk0_1_checked, root1Node47Step2Chunk0_2_checked, root1Node47Step2Chunk0_3_checked, root1Node47Step2Chunk0_4_checked, root1Node47Step2Chunk0_5_checked, root1Node47Step2Chunk1_0_checked, root1Node47Step2Chunk1_1_checked, root1Node47Step2Chunk1_2_checked, root1Node47Step2Chunk1_3_checked, root1Node47Step2Chunk1_4_checked, root1Node47Step2Chunk1_5_checked, root1Node47Step2Chunk2_0_checked, root1Node47Step2Chunk2_1_checked, root1Node47Step2Chunk2_2_checked, root1Node47Step2Chunk2_3_checked, root1Node47Step2Chunk2_4_checked, root1Node47Step2Chunk2_5_checked, root1Node47Step2Chunk3_0_checked, root1Node47Step2Chunk3_1_checked, root1Node47Step2Chunk3_2_checked, root1Node47Step2Chunk3_3_checked, root1Node47Step2Chunk3_4_checked, root1Node47Step2Chunk3_5_checked, root1Node47Step2Chunk4_0_checked, root1Node47Step2Chunk4_1_checked, root1Node47Step2Chunk4_2_checked, root1Node47Step2Chunk4_3_checked, root1Node47Step2Chunk4_4_checked, root1Node47Step2Chunk4_5_checked, root1Node47Step2Chunk5_0_checked, root1Node47Step2Chunk5_1_checked, root1Node47Step2Chunk5_2_checked, root1Node47Step2Chunk5_3_checked, root1Node47Step2Chunk5_4_checked, root1Node47Step2Chunk5_5_checked, root1Node47Step2Chunk6_0_checked, root1Node47Step2Chunk6_1_checked, root1Node47Step2Chunk6_2_checked, root1Node47Step2Chunk6_3_checked, root1Node47Step2Chunk6_4_checked, root1Node47Step2Chunk6_5_checked, root1Node47Step2Chunk7_0_checked, root1Node47Step2Chunk7_1_checked, root1Node47Step2Chunk7_2_checked, root1Node47Step2Chunk7_3_checked, root1Node47Step2Chunk7_4_checked, root1Node47Step2Chunk7_5_checked, root1Node47Step2Chunk8_0_checked, root1Node47Step2Chunk8_1_checked, root1Node47Step2Chunk8_2_checked, root1Node47Step2Chunk8_3_checked, root1Node47Step2Chunk8_4_checked, root1Node47Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root1Node47Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node47Domains2 (.output 22) = true := by decide
def root1Node48Domains0 : Domains 61 State := restrict root1Node46Domains1 26 (8,5)
def root1Node48Domains0Fast (v : Fin 61) : Option (List State) :=
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
  | 26 => some [(8,5)]
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
theorem root1Node48Domains0_fast_eq : root1Node48Domains0 = expandDomains root1Node48Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node48Domains0 v = expandDomains root1Node48Domains0Fast v from by decide) v
def root1Node49Domains0 : Domains 61 State := restrict root1Node48Domains0 37 (1,3)
def root1Node49Domains0Fast (v : Fin 61) : Option (List State) :=
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
  | 26 => some [(8,5)]
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
  | 37 => some [(1,3)]
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
theorem root1Node49Domains0_fast_eq : root1Node49Domains0 = expandDomains root1Node49Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node49Domains0 v = expandDomains root1Node49Domains0Fast v from by decide) v
def root1Node49Domains1 (v : Fin 61) : List State :=
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
  | 26 => [(8,5)]
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
  | 37 => [(1,3)]
  | 38 => [(8,2)]
  | 39 => [(8,0)]
  | 40 => [(7,3)]
  | 41 => [(4,2)]
  | 42 => [(5,3)]
  | 43 => [(8,1)]
  | 44 => [(6,5)]
  | 45 => [(0,4)]
  | 46 => [(5,4)]
  | 47 => [(6,4)]
  | 48 => [(1,2)]
  | 49 => [(7,4)]
  | 50 => [(5,5)]
  | 51 => [(7,0)]
  | 52 => [(4,3)]
  | 53 => [(3,5)]
  | 54 => [(0,3)]
  | 55 => [(4,1)]
  | 56 => [(4,4)]
  | 57 => [(1,4)]
  | 58 => [(0,5)]
  | 59 => [(2,4)]
  | _ => [(1,3)]
def root1Node49Domains1Fast (v : Fin 61) : Option (List State) :=
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
  | 26 => some [(8,5)]
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
  | 37 => some [(1,3)]
  | 38 => some [(8,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(8,1)]
  | 44 => some [(6,5)]
  | 45 => some [(0,4)]
  | 46 => some [(5,4)]
  | 47 => some [(6,4)]
  | 48 => some [(1,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,5)]
  | 51 => some [(7,0)]
  | 52 => some [(4,3)]
  | 53 => some [(3,5)]
  | 54 => some [(0,3)]
  | 55 => some [(4,1)]
  | 56 => some [(4,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(2,4)]
  | _ => some [(1,3)]
theorem root1Node49Domains1_fast_eq : root1Node49Domains1 = expandDomains root1Node49Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node49Domains1 v = expandDomains root1Node49Domains1Fast v from by decide) v
theorem root1Node49Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root1Node49Domains0 root1Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node49Domains0 root1Node49Domains1
    root1Node49Domains0Fast root1Node49Domains1Fast
    root1Node49Domains0_fast_eq root1Node49Domains1_fast_eq (by decide)
theorem root1Node49Step1_checked :
    checkReplacement table46 root1Node49Domains0 root1Node49Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node49Step1Chunk0_0_checked, root1Node49Step1Chunk0_1_checked, root1Node49Step1Chunk0_2_checked, root1Node49Step1Chunk0_3_checked, root1Node49Step1Chunk0_4_checked, root1Node49Step1Chunk0_5_checked, root1Node49Step1Chunk1_0_checked, root1Node49Step1Chunk1_1_checked, root1Node49Step1Chunk1_2_checked, root1Node49Step1Chunk1_3_checked, root1Node49Step1Chunk1_4_checked, root1Node49Step1Chunk1_5_checked, root1Node49Step1Chunk2_0_checked, root1Node49Step1Chunk2_1_checked, root1Node49Step1Chunk2_2_checked, root1Node49Step1Chunk2_3_checked, root1Node49Step1Chunk2_4_checked, root1Node49Step1Chunk2_5_checked, root1Node49Step1Chunk3_0_checked, root1Node49Step1Chunk3_1_checked, root1Node49Step1Chunk3_2_checked, root1Node49Step1Chunk3_3_checked, root1Node49Step1Chunk3_4_checked, root1Node49Step1Chunk3_5_checked, root1Node49Step1Chunk4_0_checked, root1Node49Step1Chunk4_1_checked, root1Node49Step1Chunk4_2_checked, root1Node49Step1Chunk4_3_checked, root1Node49Step1Chunk4_4_checked, root1Node49Step1Chunk4_5_checked, root1Node49Step1Chunk5_0_checked, root1Node49Step1Chunk5_1_checked, root1Node49Step1Chunk5_2_checked, root1Node49Step1Chunk5_3_checked, root1Node49Step1Chunk5_4_checked, root1Node49Step1Chunk5_5_checked, root1Node49Step1Chunk6_0_checked, root1Node49Step1Chunk6_1_checked, root1Node49Step1Chunk6_2_checked, root1Node49Step1Chunk6_3_checked, root1Node49Step1Chunk6_4_checked, root1Node49Step1Chunk6_5_checked, root1Node49Step1Chunk7_0_checked, root1Node49Step1Chunk7_1_checked, root1Node49Step1Chunk7_2_checked, root1Node49Step1Chunk7_3_checked, root1Node49Step1Chunk7_4_checked, root1Node49Step1Chunk7_5_checked, root1Node49Step1Chunk8_0_checked, root1Node49Step1Chunk8_1_checked, root1Node49Step1Chunk8_2_checked, root1Node49Step1Chunk8_3_checked, root1Node49Step1Chunk8_4_checked, root1Node49Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root1Node49Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node49Domains1 (.output 23) = true := by decide
def root1Node50Domains0 : Domains 61 State := restrict root1Node48Domains0 37 (6,3)
def root1Node50Domains0Fast (v : Fin 61) : Option (List State) :=
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
  | 26 => some [(8,5)]
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
theorem root1Node50Domains0_fast_eq : root1Node50Domains0 = expandDomains root1Node50Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node50Domains0 v = expandDomains root1Node50Domains0Fast v from by decide) v
def root1Node50Domains1 (v : Fin 61) : List State :=
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
  | 26 => [(8,5)]
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
  | 48 => [(6,2)]
  | 49 => [(7,4)]
  | 50 => [(5,2)]
  | 51 => [(8,0)]
  | 52 => [(8,3)]
  | 53 => [(5,5)]
  | 54 => [(1,0)]
  | 55 => [(2,1)]
  | 56 => [(8,4)]
  | 57 => [(1,4)]
  | 58 => [(0,5)]
  | 59 => [(4,4)]
  | _ => [(0,0)]
def root1Node50Domains1Fast (v : Fin 61) : Option (List State) :=
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
  | 26 => some [(8,5)]
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
  | 48 => some [(6,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,2)]
  | 51 => some [(8,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5)]
  | 54 => some [(1,0)]
  | 55 => some [(2,1)]
  | 56 => some [(8,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(4,4)]
  | _ => some [(0,0)]
theorem root1Node50Domains1_fast_eq : root1Node50Domains1 = expandDomains root1Node50Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node50Domains1 v = expandDomains root1Node50Domains1Fast v from by decide) v
theorem root1Node50Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1_checked :
    checkReplacement table46 root1Node50Domains0 root1Node50Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node50Step1Chunk0_0_checked, root1Node50Step1Chunk0_1_checked, root1Node50Step1Chunk0_2_checked, root1Node50Step1Chunk0_3_checked, root1Node50Step1Chunk0_4_checked, root1Node50Step1Chunk0_5_checked, root1Node50Step1Chunk1_0_checked, root1Node50Step1Chunk1_1_checked, root1Node50Step1Chunk1_2_checked, root1Node50Step1Chunk1_3_checked, root1Node50Step1Chunk1_4_checked, root1Node50Step1Chunk1_5_checked, root1Node50Step1Chunk2_0_checked, root1Node50Step1Chunk2_1_checked, root1Node50Step1Chunk2_2_checked, root1Node50Step1Chunk2_3_checked, root1Node50Step1Chunk2_4_checked, root1Node50Step1Chunk2_5_checked, root1Node50Step1Chunk3_0_checked, root1Node50Step1Chunk3_1_checked, root1Node50Step1Chunk3_2_checked, root1Node50Step1Chunk3_3_checked, root1Node50Step1Chunk3_4_checked, root1Node50Step1Chunk3_5_checked, root1Node50Step1Chunk4_0_checked, root1Node50Step1Chunk4_1_checked, root1Node50Step1Chunk4_2_checked, root1Node50Step1Chunk4_3_checked, root1Node50Step1Chunk4_4_checked, root1Node50Step1Chunk4_5_checked, root1Node50Step1Chunk5_0_checked, root1Node50Step1Chunk5_1_checked, root1Node50Step1Chunk5_2_checked, root1Node50Step1Chunk5_3_checked, root1Node50Step1Chunk5_4_checked, root1Node50Step1Chunk5_5_checked, root1Node50Step1Chunk6_0_checked, root1Node50Step1Chunk6_1_checked, root1Node50Step1Chunk6_2_checked, root1Node50Step1Chunk6_3_checked, root1Node50Step1Chunk6_4_checked, root1Node50Step1Chunk6_5_checked, root1Node50Step1Chunk7_0_checked, root1Node50Step1Chunk7_1_checked, root1Node50Step1Chunk7_2_checked, root1Node50Step1Chunk7_3_checked, root1Node50Step1Chunk7_4_checked, root1Node50Step1Chunk7_5_checked, root1Node50Step1Chunk8_0_checked, root1Node50Step1Chunk8_1_checked, root1Node50Step1Chunk8_2_checked, root1Node50Step1Chunk8_3_checked, root1Node50Step1Chunk8_4_checked, root1Node50Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root1Node50Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node50Domains1 (.output 24) = true := by decide
def root1Node51Domains0 : Domains 61 State := restrict root1Node43Domains4 3 (6,4)
def root1Node51Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(6,4)]
  | 4 => some [(0,5),(1,2)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(1,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3),(6,0)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2),(8,2)]
  | 16 => some [(5,0),(5,3),(8,0)]
  | 17 => some [(4,5),(7,3),(8,5)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(7,4),(8,4)]
  | 24 => some [(0,0),(6,3),(6,4)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(4,5),(5,2),(5,5),(8,5)]
  | 27 => some [(7,0),(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5),(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(2,1),(7,1)]
  | 32 => some [(0,2),(1,5),(7,5)]
  | 33 => some [(0,3),(1,1),(6,1)]
  | 34 => some [(4,1),(8,1)]
  | 35 => some [(4,4),(5,4),(7,2),(8,4)]
  | 36 => some [(1,4),(7,4)]
  | 37 => some [(0,5),(1,3),(6,3)]
  | 38 => some [(4,4),(7,2),(8,2)]
  | 39 => some [(0,0),(4,0),(5,0),(8,0)]
  | 40 => some [(3,2),(4,5),(7,3)]
  | 41 => some [(4,0),(4,2),(7,0)]
  | 42 => some [(5,3),(7,3),(8,3)]
  | 43 => some [(4,1),(7,5),(8,1)]
  | 44 => some [(0,2),(6,0),(6,5)]
  | 45 => some [(0,4),(1,1),(7,1)]
  | 46 => some [(1,5),(5,1),(5,4)]
  | 47 => some [(0,0),(0,1),(6,1),(6,4)]
  | 48 => some [(1,2),(5,1),(6,2),(7,2)]
  | 49 => some [(0,1),(7,4)]
  | 50 => some [(5,2),(5,5),(8,2)]
  | 51 => some [(5,0),(7,0),(8,0)]
  | 52 => some [(4,3),(4,5),(8,3)]
  | 53 => some [(1,5),(3,5),(5,5),(7,0)]
  | 54 => some [(0,3),(1,0),(6,1),(8,3)]
  | 55 => some [(2,1),(4,1),(8,5)]
  | 56 => some [(4,4),(5,4),(8,4)]
  | 57 => some [(0,0),(1,4)]
  | 58 => some [(0,5),(7,2)]
  | 59 => some [(2,0),(2,4),(4,4),(7,4)]
  | _ => some [(0,0),(1,3),(6,3),(7,3)]
theorem root1Node51Domains0_fast_eq : root1Node51Domains0 = expandDomains root1Node51Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node51Domains0 v = expandDomains root1Node51Domains0Fast v from by decide) v
def root1Node51Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(4,5),(8,5)]
  | 6 => [(1,0)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(0,0),(6,3)]
  | 12 => [(7,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(0,2),(1,5)]
  | 19 => [(1,1),(6,1)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(7,4)]
  | 24 => [(6,3)]
  | 25 => [(7,2)]
  | 26 => [(4,5),(5,2),(5,5),(8,5)]
  | 27 => [(7,0),(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(1,0)]
  | 31 => [(2,1)]
  | 32 => [(0,2)]
  | 33 => [(1,1)]
  | 34 => [(4,1),(8,1)]
  | 35 => [(4,4),(5,4),(7,2),(8,4)]
  | 36 => [(1,4),(7,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(0,0)]
  | 40 => [(3,2)]
  | 41 => [(4,0)]
  | 42 => [(5,3),(7,3),(8,3)]
  | 43 => [(4,1),(7,5),(8,1)]
  | 44 => [(0,2),(6,0),(6,5)]
  | 45 => [(7,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1)]
  | 49 => [(0,1),(7,4)]
  | 50 => [(5,2),(5,5),(8,2)]
  | 51 => [(5,0),(7,0),(8,0)]
  | 52 => [(4,3),(4,5),(8,3)]
  | 53 => [(1,5),(3,5),(5,5),(7,0)]
  | 54 => [(0,3),(1,0),(6,1),(8,3)]
  | 55 => [(2,1),(4,1),(8,5)]
  | 56 => [(4,4),(5,4),(8,4)]
  | 57 => [(0,0),(1,4)]
  | 58 => [(0,5),(7,2)]
  | 59 => [(2,0),(2,4),(4,4),(7,4)]
  | _ => [(0,0),(1,3),(6,3),(7,3)]
def root1Node51Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(1,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(7,4)]
  | 24 => some [(6,3)]
  | 25 => some [(7,2)]
  | 26 => some [(4,5),(5,2),(5,5),(8,5)]
  | 27 => some [(7,0),(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(1,0)]
  | 31 => some [(2,1)]
  | 32 => some [(0,2)]
  | 33 => some [(1,1)]
  | 34 => some [(4,1),(8,1)]
  | 35 => some [(4,4),(5,4),(7,2),(8,4)]
  | 36 => some [(1,4),(7,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(0,0)]
  | 40 => some [(3,2)]
  | 41 => some [(4,0)]
  | 42 => some [(5,3),(7,3),(8,3)]
  | 43 => some [(4,1),(7,5),(8,1)]
  | 44 => some [(0,2),(6,0),(6,5)]
  | 45 => some [(7,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1),(7,4)]
  | 50 => some [(5,2),(5,5),(8,2)]
  | 51 => some [(5,0),(7,0),(8,0)]
  | 52 => some [(4,3),(4,5),(8,3)]
  | 53 => some [(1,5),(3,5),(5,5),(7,0)]
  | 54 => some [(0,3),(1,0),(6,1),(8,3)]
  | 55 => some [(2,1),(4,1),(8,5)]
  | 56 => some [(4,4),(5,4),(8,4)]
  | 57 => some [(0,0),(1,4)]
  | 58 => some [(0,5),(7,2)]
  | 59 => some [(2,0),(2,4),(4,4),(7,4)]
  | _ => some [(0,0),(1,3),(6,3),(7,3)]
theorem root1Node51Domains1_fast_eq : root1Node51Domains1 = expandDomains root1Node51Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node51Domains1 v = expandDomains root1Node51Domains1Fast v from by decide) v
theorem root1Node51Step1Chunk0_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_0⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk0_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_1⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk0_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_2⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk0_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_3⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk0_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_4⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk0_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_5⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk1_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_0⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk1_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_1⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk1_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_2⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk1_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_3⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk1_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_4⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk1_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_5⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk2_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_0⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk2_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_1⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk2_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_2⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk2_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_3⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk2_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_4⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk2_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_5⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk3_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_0⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk3_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_1⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk3_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_2⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk3_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_3⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk3_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_4⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk3_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_5⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk4_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_0⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk4_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_1⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk4_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_2⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk4_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_3⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk4_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_4⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk4_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_5⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk5_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_0⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk5_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_1⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk5_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_2⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk5_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_3⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk5_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_4⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk5_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_5⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk6_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_0⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk6_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_1⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk6_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_2⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk6_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_3⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk6_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_4⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk6_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_5⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk7_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_0⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk7_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_1⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk7_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_2⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk7_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_3⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk7_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_4⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk7_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_5⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk8_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_0⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk8_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_1⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk8_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_2⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk8_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_3⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk8_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_4⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1Chunk8_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_5⟩
      root1Node51Domains0 root1Node51Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains0 root1Node51Domains1
    root1Node51Domains0Fast root1Node51Domains1Fast
    root1Node51Domains0_fast_eq root1Node51Domains1_fast_eq (by decide)
theorem root1Node51Step1_checked :
    checkReplacement table22 root1Node51Domains0 root1Node51Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node51Step1Chunk0_0_checked, root1Node51Step1Chunk0_1_checked, root1Node51Step1Chunk0_2_checked, root1Node51Step1Chunk0_3_checked, root1Node51Step1Chunk0_4_checked, root1Node51Step1Chunk0_5_checked, root1Node51Step1Chunk1_0_checked, root1Node51Step1Chunk1_1_checked, root1Node51Step1Chunk1_2_checked, root1Node51Step1Chunk1_3_checked, root1Node51Step1Chunk1_4_checked, root1Node51Step1Chunk1_5_checked, root1Node51Step1Chunk2_0_checked, root1Node51Step1Chunk2_1_checked, root1Node51Step1Chunk2_2_checked, root1Node51Step1Chunk2_3_checked, root1Node51Step1Chunk2_4_checked, root1Node51Step1Chunk2_5_checked, root1Node51Step1Chunk3_0_checked, root1Node51Step1Chunk3_1_checked, root1Node51Step1Chunk3_2_checked, root1Node51Step1Chunk3_3_checked, root1Node51Step1Chunk3_4_checked, root1Node51Step1Chunk3_5_checked, root1Node51Step1Chunk4_0_checked, root1Node51Step1Chunk4_1_checked, root1Node51Step1Chunk4_2_checked, root1Node51Step1Chunk4_3_checked, root1Node51Step1Chunk4_4_checked, root1Node51Step1Chunk4_5_checked, root1Node51Step1Chunk5_0_checked, root1Node51Step1Chunk5_1_checked, root1Node51Step1Chunk5_2_checked, root1Node51Step1Chunk5_3_checked, root1Node51Step1Chunk5_4_checked, root1Node51Step1Chunk5_5_checked, root1Node51Step1Chunk6_0_checked, root1Node51Step1Chunk6_1_checked, root1Node51Step1Chunk6_2_checked, root1Node51Step1Chunk6_3_checked, root1Node51Step1Chunk6_4_checked, root1Node51Step1Chunk6_5_checked, root1Node51Step1Chunk7_0_checked, root1Node51Step1Chunk7_1_checked, root1Node51Step1Chunk7_2_checked, root1Node51Step1Chunk7_3_checked, root1Node51Step1Chunk7_4_checked, root1Node51Step1Chunk7_5_checked, root1Node51Step1Chunk8_0_checked, root1Node51Step1Chunk8_1_checked, root1Node51Step1Chunk8_2_checked, root1Node51Step1Chunk8_3_checked, root1Node51Step1Chunk8_4_checked, root1Node51Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
