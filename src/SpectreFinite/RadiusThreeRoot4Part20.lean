module

public import SpectreFinite.RadiusThreeRoot4Part19
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable24
public import SpectreFinite.RadiusThreeTable26

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node33Domains0 : Domains 37 State := restrict root4Node32Domains2 21 (5,0)
def root4Node33Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(2,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(3,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(8,4)]
  | 8 => some [(1,4)]
  | 9 => some [(5,0)]
  | 10 => some [(4,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(6,0)]
  | 15 => some [(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(1,5)]
  | 23 => some [(6,1)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(8,4)]
  | 28 => some [(7,0)]
  | 29 => some [(8,3)]
  | 30 => some [(8,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,4)]
  | 34 => some [(1,3),(6,3)]
  | 35 => some [(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root4Node33Domains0_fast_eq : root4Node33Domains0 = expandDomains root4Node33Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node33Domains0 v = expandDomains root4Node33Domains0Fast v from by decide) v
def root4Node33Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(2,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(3,1)]
  | 5 => [(0,1)]
  | 6 => [(6,2)]
  | 7 => [(8,4)]
  | 8 => [(1,4)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(1,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(6,0)]
  | 15 => [(8,4)]
  | 16 => [(0,0)]
  | 17 => [(7,2)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(1,5)]
  | 23 => [(6,1)]
  | 24 => [(5,1)]
  | 25 => [(0,1)]
  | 26 => [(6,2)]
  | 27 => [(8,4)]
  | 28 => [(7,0)]
  | 29 => [(8,3)]
  | 30 => [(8,5)]
  | 31 => [(1,0)]
  | 32 => [(7,1)]
  | 33 => [(7,4)]
  | 34 => [(1,3),(6,3)]
  | 35 => [(8,2)]
  | _ => [(5,0)]
def root4Node33Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(2,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(3,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(8,4)]
  | 8 => some [(1,4)]
  | 9 => some [(5,0)]
  | 10 => some [(4,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(6,0)]
  | 15 => some [(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(1,5)]
  | 23 => some [(6,1)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(8,4)]
  | 28 => some [(7,0)]
  | 29 => some [(8,3)]
  | 30 => some [(8,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,4)]
  | 34 => some [(1,3),(6,3)]
  | 35 => some [(8,2)]
  | _ => some [(5,0)]
theorem root4Node33Domains1_fast_eq : root4Node33Domains1 = expandDomains root4Node33Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node33Domains1 v = expandDomains root4Node33Domains1Fast v from by decide) v
theorem root4Node33Step1Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root4Node33Domains0 root4Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains0 root4Node33Domains1
    root4Node33Domains0Fast root4Node33Domains1Fast
    root4Node33Domains0_fast_eq root4Node33Domains1_fast_eq (by decide)
theorem root4Node33Step1_checked :
    checkReplacement table26 root4Node33Domains0 root4Node33Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node33Step1Chunk0_0_checked, root4Node33Step1Chunk0_1_checked, root4Node33Step1Chunk0_2_checked, root4Node33Step1Chunk0_3_checked, root4Node33Step1Chunk0_4_checked, root4Node33Step1Chunk0_5_checked, root4Node33Step1Chunk1_0_checked, root4Node33Step1Chunk1_1_checked, root4Node33Step1Chunk1_2_checked, root4Node33Step1Chunk1_3_checked, root4Node33Step1Chunk1_4_checked, root4Node33Step1Chunk1_5_checked, root4Node33Step1Chunk2_0_checked, root4Node33Step1Chunk2_1_checked, root4Node33Step1Chunk2_2_checked, root4Node33Step1Chunk2_3_checked, root4Node33Step1Chunk2_4_checked, root4Node33Step1Chunk2_5_checked, root4Node33Step1Chunk3_0_checked, root4Node33Step1Chunk3_1_checked, root4Node33Step1Chunk3_2_checked, root4Node33Step1Chunk3_3_checked, root4Node33Step1Chunk3_4_checked, root4Node33Step1Chunk3_5_checked, root4Node33Step1Chunk4_0_checked, root4Node33Step1Chunk4_1_checked, root4Node33Step1Chunk4_2_checked, root4Node33Step1Chunk4_3_checked, root4Node33Step1Chunk4_4_checked, root4Node33Step1Chunk4_5_checked, root4Node33Step1Chunk5_0_checked, root4Node33Step1Chunk5_1_checked, root4Node33Step1Chunk5_2_checked, root4Node33Step1Chunk5_3_checked, root4Node33Step1Chunk5_4_checked, root4Node33Step1Chunk5_5_checked, root4Node33Step1Chunk6_0_checked, root4Node33Step1Chunk6_1_checked, root4Node33Step1Chunk6_2_checked, root4Node33Step1Chunk6_3_checked, root4Node33Step1Chunk6_4_checked, root4Node33Step1Chunk6_5_checked, root4Node33Step1Chunk7_0_checked, root4Node33Step1Chunk7_1_checked, root4Node33Step1Chunk7_2_checked, root4Node33Step1Chunk7_3_checked, root4Node33Step1Chunk7_4_checked, root4Node33Step1Chunk7_5_checked, root4Node33Step1Chunk8_0_checked, root4Node33Step1Chunk8_1_checked, root4Node33Step1Chunk8_2_checked, root4Node33Step1Chunk8_3_checked, root4Node33Step1Chunk8_4_checked, root4Node33Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node33Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(2,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(3,1)]
  | 5 => [(0,1)]
  | 6 => [(6,2)]
  | 7 => [(8,4)]
  | 8 => [(1,4)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(1,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(6,0)]
  | 15 => [(8,4)]
  | 16 => [(0,0)]
  | 17 => [(7,2)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(1,5)]
  | 23 => [(6,1)]
  | 24 => [(5,1)]
  | 25 => [(0,1)]
  | 26 => [(6,2)]
  | 27 => [(8,4)]
  | 28 => [(7,0)]
  | 29 => [(8,3)]
  | 30 => [(8,5)]
  | 31 => [(1,0)]
  | 32 => [(7,1)]
  | 33 => [(7,4)]
  | 34 => [(1,3)]
  | 35 => [(8,2)]
  | _ => [(5,0)]
def root4Node33Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(2,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(3,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(8,4)]
  | 8 => some [(1,4)]
  | 9 => some [(5,0)]
  | 10 => some [(4,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(6,0)]
  | 15 => some [(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(1,5)]
  | 23 => some [(6,1)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(8,4)]
  | 28 => some [(7,0)]
  | 29 => some [(8,3)]
  | 30 => some [(8,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,4)]
  | 34 => some [(1,3)]
  | 35 => some [(8,2)]
  | _ => some [(5,0)]
theorem root4Node33Domains2_fast_eq : root4Node33Domains2 = expandDomains root4Node33Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node33Domains2 v = expandDomains root4Node33Domains2Fast v from by decide) v
theorem root4Node33Step2Chunk0_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_0⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk0_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_1⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk0_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_2⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk0_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_3⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk0_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_4⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk0_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows0_5⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk1_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_0⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk1_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_1⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk1_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_2⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk1_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_3⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk1_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_4⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk1_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows1_5⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk2_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_0⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk2_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_1⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk2_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_2⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk2_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_3⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk2_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_4⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk2_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows2_5⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk3_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_0⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk3_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_1⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk3_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_2⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk3_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_3⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk3_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_4⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk3_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows3_5⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk4_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_0⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk4_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_1⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk4_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_2⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk4_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_3⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk4_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_4⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk4_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows4_5⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk5_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_0⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk5_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_1⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk5_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_2⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk5_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_3⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk5_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_4⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk5_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows5_5⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk6_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_0⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk6_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_1⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk6_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_2⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk6_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_3⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk6_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_4⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk6_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows6_5⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk7_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_0⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk7_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_1⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk7_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_2⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk7_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_3⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk7_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_4⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk7_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows7_5⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk8_0_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_0⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk8_1_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_1⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk8_2_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_2⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk8_3_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_3⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk8_4_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_4⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2Chunk8_5_checked :
    checkNarrowing ⟨table24Scope, table24Rows8_5⟩
      root4Node33Domains1 root4Node33Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node33Domains1 root4Node33Domains2
    root4Node33Domains1Fast root4Node33Domains2Fast
    root4Node33Domains1_fast_eq root4Node33Domains2_fast_eq (by decide)
theorem root4Node33Step2_checked :
    checkReplacement table24 root4Node33Domains1 root4Node33Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node33Step2Chunk0_0_checked, root4Node33Step2Chunk0_1_checked, root4Node33Step2Chunk0_2_checked, root4Node33Step2Chunk0_3_checked, root4Node33Step2Chunk0_4_checked, root4Node33Step2Chunk0_5_checked, root4Node33Step2Chunk1_0_checked, root4Node33Step2Chunk1_1_checked, root4Node33Step2Chunk1_2_checked, root4Node33Step2Chunk1_3_checked, root4Node33Step2Chunk1_4_checked, root4Node33Step2Chunk1_5_checked, root4Node33Step2Chunk2_0_checked, root4Node33Step2Chunk2_1_checked, root4Node33Step2Chunk2_2_checked, root4Node33Step2Chunk2_3_checked, root4Node33Step2Chunk2_4_checked, root4Node33Step2Chunk2_5_checked, root4Node33Step2Chunk3_0_checked, root4Node33Step2Chunk3_1_checked, root4Node33Step2Chunk3_2_checked, root4Node33Step2Chunk3_3_checked, root4Node33Step2Chunk3_4_checked, root4Node33Step2Chunk3_5_checked, root4Node33Step2Chunk4_0_checked, root4Node33Step2Chunk4_1_checked, root4Node33Step2Chunk4_2_checked, root4Node33Step2Chunk4_3_checked, root4Node33Step2Chunk4_4_checked, root4Node33Step2Chunk4_5_checked, root4Node33Step2Chunk5_0_checked, root4Node33Step2Chunk5_1_checked, root4Node33Step2Chunk5_2_checked, root4Node33Step2Chunk5_3_checked, root4Node33Step2Chunk5_4_checked, root4Node33Step2Chunk5_5_checked, root4Node33Step2Chunk6_0_checked, root4Node33Step2Chunk6_1_checked, root4Node33Step2Chunk6_2_checked, root4Node33Step2Chunk6_3_checked, root4Node33Step2Chunk6_4_checked, root4Node33Step2Chunk6_5_checked, root4Node33Step2Chunk7_0_checked, root4Node33Step2Chunk7_1_checked, root4Node33Step2Chunk7_2_checked, root4Node33Step2Chunk7_3_checked, root4Node33Step2Chunk7_4_checked, root4Node33Step2Chunk7_5_checked, root4Node33Step2Chunk8_0_checked, root4Node33Step2Chunk8_1_checked, root4Node33Step2Chunk8_2_checked, root4Node33Step2Chunk8_3_checked, root4Node33Step2Chunk8_4_checked, root4Node33Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root4Node33Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node33Domains2 (.output 15) = true := by decide
def root4Node34Domains0 : Domains 37 State := restrict root4Node32Domains2 21 (8,0)
def root4Node34Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(2,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(3,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(8,4)]
  | 8 => some [(1,4)]
  | 9 => some [(5,0)]
  | 10 => some [(4,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(6,0)]
  | 15 => some [(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(8,0)]
  | 22 => some [(1,5)]
  | 23 => some [(6,1)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(8,4)]
  | 28 => some [(7,0)]
  | 29 => some [(8,3)]
  | 30 => some [(8,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,4)]
  | 34 => some [(1,3),(6,3)]
  | 35 => some [(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root4Node34Domains0_fast_eq : root4Node34Domains0 = expandDomains root4Node34Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node34Domains0 v = expandDomains root4Node34Domains0Fast v from by decide) v
def root4Node34Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(2,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(3,1)]
  | 5 => [(0,1)]
  | 6 => [(6,2)]
  | 7 => [(8,4)]
  | 8 => [(1,4)]
  | 9 => [(5,0)]
  | 10 => [(4,5)]
  | 11 => [(1,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(6,0)]
  | 15 => [(8,4)]
  | 16 => [(0,0)]
  | 17 => [(7,2)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(8,0)]
  | 22 => [(1,5)]
  | 23 => [(6,1)]
  | 24 => [(5,1)]
  | 25 => [(0,1)]
  | 26 => [(6,2)]
  | 27 => [(8,4)]
  | 28 => [(7,0)]
  | 29 => [(8,3)]
  | 30 => [(8,5)]
  | 31 => [(1,0)]
  | 32 => [(7,1)]
  | 33 => [(7,4)]
  | 34 => [(1,3),(6,3)]
  | 35 => [(7,2),(8,2)]
  | _ => [(4,0),(8,0)]
def root4Node34Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(2,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(3,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(8,4)]
  | 8 => some [(1,4)]
  | 9 => some [(5,0)]
  | 10 => some [(4,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(6,0)]
  | 15 => some [(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(8,0)]
  | 22 => some [(1,5)]
  | 23 => some [(6,1)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(8,4)]
  | 28 => some [(7,0)]
  | 29 => some [(8,3)]
  | 30 => some [(8,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,4)]
  | 34 => some [(1,3),(6,3)]
  | 35 => some [(7,2),(8,2)]
  | _ => some [(4,0),(8,0)]
theorem root4Node34Domains1_fast_eq : root4Node34Domains1 = expandDomains root4Node34Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node34Domains1 v = expandDomains root4Node34Domains1Fast v from by decide) v
theorem root4Node34Step1Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root4Node34Domains0 root4Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node34Domains0 root4Node34Domains1
    root4Node34Domains0Fast root4Node34Domains1Fast
    root4Node34Domains0_fast_eq root4Node34Domains1_fast_eq (by decide)
theorem root4Node34Step1_checked :
    checkReplacement table26 root4Node34Domains0 root4Node34Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node34Step1Chunk0_0_checked, root4Node34Step1Chunk0_1_checked, root4Node34Step1Chunk0_2_checked, root4Node34Step1Chunk0_3_checked, root4Node34Step1Chunk0_4_checked, root4Node34Step1Chunk0_5_checked, root4Node34Step1Chunk1_0_checked, root4Node34Step1Chunk1_1_checked, root4Node34Step1Chunk1_2_checked, root4Node34Step1Chunk1_3_checked, root4Node34Step1Chunk1_4_checked, root4Node34Step1Chunk1_5_checked, root4Node34Step1Chunk2_0_checked, root4Node34Step1Chunk2_1_checked, root4Node34Step1Chunk2_2_checked, root4Node34Step1Chunk2_3_checked, root4Node34Step1Chunk2_4_checked, root4Node34Step1Chunk2_5_checked, root4Node34Step1Chunk3_0_checked, root4Node34Step1Chunk3_1_checked, root4Node34Step1Chunk3_2_checked, root4Node34Step1Chunk3_3_checked, root4Node34Step1Chunk3_4_checked, root4Node34Step1Chunk3_5_checked, root4Node34Step1Chunk4_0_checked, root4Node34Step1Chunk4_1_checked, root4Node34Step1Chunk4_2_checked, root4Node34Step1Chunk4_3_checked, root4Node34Step1Chunk4_4_checked, root4Node34Step1Chunk4_5_checked, root4Node34Step1Chunk5_0_checked, root4Node34Step1Chunk5_1_checked, root4Node34Step1Chunk5_2_checked, root4Node34Step1Chunk5_3_checked, root4Node34Step1Chunk5_4_checked, root4Node34Step1Chunk5_5_checked, root4Node34Step1Chunk6_0_checked, root4Node34Step1Chunk6_1_checked, root4Node34Step1Chunk6_2_checked, root4Node34Step1Chunk6_3_checked, root4Node34Step1Chunk6_4_checked, root4Node34Step1Chunk6_5_checked, root4Node34Step1Chunk7_0_checked, root4Node34Step1Chunk7_1_checked, root4Node34Step1Chunk7_2_checked, root4Node34Step1Chunk7_3_checked, root4Node34Step1Chunk7_4_checked, root4Node34Step1Chunk7_5_checked, root4Node34Step1Chunk8_0_checked, root4Node34Step1Chunk8_1_checked, root4Node34Step1Chunk8_2_checked, root4Node34Step1Chunk8_3_checked, root4Node34Step1Chunk8_4_checked, root4Node34Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
