module

public import SpectreFinite.RadiusThreeRoot7Part32
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable26

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node49Domains0 : Domains 37 State := restrict root7Node45Domains7 14 (6,4)
def root7Node49Domains0Fast (v : Fin 37) : Option (List State) :=
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
  | 14 => some [(6,4)]
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
  | 26 => some [(1,3)]
  | 27 => some [(4,2),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(8,1)]
  | 31 => some [(6,5)]
  | 32 => some [(0,4)]
  | 33 => some [(7,0)]
  | 34 => some [(8,3)]
  | 35 => some [(5,5),(8,5)]
  | _ => some [(3,0),(7,0)]
theorem root7Node49Domains0_fast_eq : root7Node49Domains0 = expandDomains root7Node49Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node49Domains0 v = expandDomains root7Node49Domains0Fast v from by decide) v
def root7Node49Domains1 (v : Fin 37) : List State :=
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
  | 14 => [(6,4)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(0,3)]
  | 22 => [(8,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(7,4)]
  | 26 => [(1,3)]
  | 27 => [(4,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(8,1)]
  | 31 => [(6,5)]
  | 32 => [(0,4)]
  | 33 => [(7,0)]
  | 34 => [(8,3)]
  | 35 => [(5,5)]
  | _ => [(3,0),(7,0)]
def root7Node49Domains1Fast (v : Fin 37) : Option (List State) :=
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
  | 14 => some [(6,4)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3)]
  | 22 => some [(8,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(1,3)]
  | 27 => some [(4,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(8,1)]
  | 31 => some [(6,5)]
  | 32 => some [(0,4)]
  | 33 => some [(7,0)]
  | 34 => some [(8,3)]
  | 35 => some [(5,5)]
  | _ => some [(3,0),(7,0)]
theorem root7Node49Domains1_fast_eq : root7Node49Domains1 = expandDomains root7Node49Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node49Domains1 v = expandDomains root7Node49Domains1Fast v from by decide) v
theorem root7Node49Step1Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root7Node49Domains0 root7Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node49Domains0 root7Node49Domains1
    root7Node49Domains0Fast root7Node49Domains1Fast
    root7Node49Domains0_fast_eq root7Node49Domains1_fast_eq (by decide)
theorem root7Node49Step1_checked :
    checkReplacement table26 root7Node49Domains0 root7Node49Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node49Step1Chunk0_0_checked, root7Node49Step1Chunk0_1_checked, root7Node49Step1Chunk0_2_checked, root7Node49Step1Chunk0_3_checked, root7Node49Step1Chunk0_4_checked, root7Node49Step1Chunk0_5_checked, root7Node49Step1Chunk1_0_checked, root7Node49Step1Chunk1_1_checked, root7Node49Step1Chunk1_2_checked, root7Node49Step1Chunk1_3_checked, root7Node49Step1Chunk1_4_checked, root7Node49Step1Chunk1_5_checked, root7Node49Step1Chunk2_0_checked, root7Node49Step1Chunk2_1_checked, root7Node49Step1Chunk2_2_checked, root7Node49Step1Chunk2_3_checked, root7Node49Step1Chunk2_4_checked, root7Node49Step1Chunk2_5_checked, root7Node49Step1Chunk3_0_checked, root7Node49Step1Chunk3_1_checked, root7Node49Step1Chunk3_2_checked, root7Node49Step1Chunk3_3_checked, root7Node49Step1Chunk3_4_checked, root7Node49Step1Chunk3_5_checked, root7Node49Step1Chunk4_0_checked, root7Node49Step1Chunk4_1_checked, root7Node49Step1Chunk4_2_checked, root7Node49Step1Chunk4_3_checked, root7Node49Step1Chunk4_4_checked, root7Node49Step1Chunk4_5_checked, root7Node49Step1Chunk5_0_checked, root7Node49Step1Chunk5_1_checked, root7Node49Step1Chunk5_2_checked, root7Node49Step1Chunk5_3_checked, root7Node49Step1Chunk5_4_checked, root7Node49Step1Chunk5_5_checked, root7Node49Step1Chunk6_0_checked, root7Node49Step1Chunk6_1_checked, root7Node49Step1Chunk6_2_checked, root7Node49Step1Chunk6_3_checked, root7Node49Step1Chunk6_4_checked, root7Node49Step1Chunk6_5_checked, root7Node49Step1Chunk7_0_checked, root7Node49Step1Chunk7_1_checked, root7Node49Step1Chunk7_2_checked, root7Node49Step1Chunk7_3_checked, root7Node49Step1Chunk7_4_checked, root7Node49Step1Chunk7_5_checked, root7Node49Step1Chunk8_0_checked, root7Node49Step1Chunk8_1_checked, root7Node49Step1Chunk8_2_checked, root7Node49Step1Chunk8_3_checked, root7Node49Step1Chunk8_4_checked, root7Node49Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node50Domains0 : Domains 37 State := restrict root7Node49Domains1 36 (3,0)
def root7Node50Domains0Fast (v : Fin 37) : Option (List State) :=
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
  | 14 => some [(6,4)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3)]
  | 22 => some [(8,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(1,3)]
  | 27 => some [(4,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(8,1)]
  | 31 => some [(6,5)]
  | 32 => some [(0,4)]
  | 33 => some [(7,0)]
  | 34 => some [(8,3)]
  | 35 => some [(5,5)]
  | _ => some [(3,0)]
theorem root7Node50Domains0_fast_eq : root7Node50Domains0 = expandDomains root7Node50Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node50Domains0 v = expandDomains root7Node50Domains0Fast v from by decide) v
theorem root7Node50Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node50Domains0 (.output 24) = true := by decide
def root7Node51Domains0 : Domains 37 State := restrict root7Node49Domains1 36 (7,0)
def root7Node51Domains0Fast (v : Fin 37) : Option (List State) :=
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
  | 14 => some [(6,4)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3)]
  | 22 => some [(8,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(1,3)]
  | 27 => some [(4,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(8,1)]
  | 31 => some [(6,5)]
  | 32 => some [(0,4)]
  | 33 => some [(7,0)]
  | 34 => some [(8,3)]
  | 35 => some [(5,5)]
  | _ => some [(7,0)]
theorem root7Node51Domains0_fast_eq : root7Node51Domains0 = expandDomains root7Node51Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node51Domains0 v = expandDomains root7Node51Domains0Fast v from by decide) v
theorem root7Node51Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node51Domains0 (.output 25) = true := by decide
end SpectreFinite.HexSearch.RadiusThree
