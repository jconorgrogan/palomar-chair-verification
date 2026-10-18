module

public import SpectreFinite.RadiusThreeRoot1Part14
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable11
public import SpectreFinite.RadiusThreeTable16
public import SpectreFinite.RadiusThreeTable26

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node27Domains0 : Domains 37 State := restrict root1Node25Domains3 14 (6,4)
def root1Node27Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(0,5)]
  | 5 => some [(2,0)]
  | 6 => some [(7,3)]
  | 7 => some [(5,2)]
  | 8 => some [(8,0)]
  | 9 => some [(6,0)]
  | 10 => some [(3,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(6,4)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(8,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(4,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(5,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(7,0)]
  | 34 => some [(8,3)]
  | 35 => some [(5,5),(8,5)]
  | _ => some [(1,0)]
theorem root1Node27Domains0_fast_eq : root1Node27Domains0 = expandDomains root1Node27Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node27Domains0 v = expandDomains root1Node27Domains0Fast v from by decide) v
def root1Node27Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(0,5)]
  | 5 => [(2,0)]
  | 6 => [(7,3)]
  | 7 => [(5,2)]
  | 8 => [(8,0)]
  | 9 => [(6,0)]
  | 10 => [(3,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(6,4)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(0,3)]
  | 22 => [(8,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(4,0)]
  | 26 => [(7,3)]
  | 27 => [(4,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(5,1)]
  | 31 => [(0,1)]
  | 32 => [(6,2)]
  | 33 => [(7,0)]
  | 34 => [(8,3)]
  | 35 => [(5,5)]
  | _ => [(1,0)]
def root1Node27Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(0,5)]
  | 5 => some [(2,0)]
  | 6 => some [(7,3)]
  | 7 => some [(5,2)]
  | 8 => some [(8,0)]
  | 9 => some [(6,0)]
  | 10 => some [(3,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(6,4)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3)]
  | 22 => some [(8,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(4,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(5,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(7,0)]
  | 34 => some [(8,3)]
  | 35 => some [(5,5)]
  | _ => some [(1,0)]
theorem root1Node27Domains1_fast_eq : root1Node27Domains1 = expandDomains root1Node27Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node27Domains1 v = expandDomains root1Node27Domains1Fast v from by decide) v
theorem root1Node27Step1Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1_checked :
    checkReplacement table26 root1Node27Domains0 root1Node27Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node27Step1Chunk0_0_checked, root1Node27Step1Chunk0_1_checked, root1Node27Step1Chunk0_2_checked, root1Node27Step1Chunk0_3_checked, root1Node27Step1Chunk0_4_checked, root1Node27Step1Chunk0_5_checked, root1Node27Step1Chunk1_0_checked, root1Node27Step1Chunk1_1_checked, root1Node27Step1Chunk1_2_checked, root1Node27Step1Chunk1_3_checked, root1Node27Step1Chunk1_4_checked, root1Node27Step1Chunk1_5_checked, root1Node27Step1Chunk2_0_checked, root1Node27Step1Chunk2_1_checked, root1Node27Step1Chunk2_2_checked, root1Node27Step1Chunk2_3_checked, root1Node27Step1Chunk2_4_checked, root1Node27Step1Chunk2_5_checked, root1Node27Step1Chunk3_0_checked, root1Node27Step1Chunk3_1_checked, root1Node27Step1Chunk3_2_checked, root1Node27Step1Chunk3_3_checked, root1Node27Step1Chunk3_4_checked, root1Node27Step1Chunk3_5_checked, root1Node27Step1Chunk4_0_checked, root1Node27Step1Chunk4_1_checked, root1Node27Step1Chunk4_2_checked, root1Node27Step1Chunk4_3_checked, root1Node27Step1Chunk4_4_checked, root1Node27Step1Chunk4_5_checked, root1Node27Step1Chunk5_0_checked, root1Node27Step1Chunk5_1_checked, root1Node27Step1Chunk5_2_checked, root1Node27Step1Chunk5_3_checked, root1Node27Step1Chunk5_4_checked, root1Node27Step1Chunk5_5_checked, root1Node27Step1Chunk6_0_checked, root1Node27Step1Chunk6_1_checked, root1Node27Step1Chunk6_2_checked, root1Node27Step1Chunk6_3_checked, root1Node27Step1Chunk6_4_checked, root1Node27Step1Chunk6_5_checked, root1Node27Step1Chunk7_0_checked, root1Node27Step1Chunk7_1_checked, root1Node27Step1Chunk7_2_checked, root1Node27Step1Chunk7_3_checked, root1Node27Step1Chunk7_4_checked, root1Node27Step1Chunk7_5_checked, root1Node27Step1Chunk8_0_checked, root1Node27Step1Chunk8_1_checked, root1Node27Step1Chunk8_2_checked, root1Node27Step1Chunk8_3_checked, root1Node27Step1Chunk8_4_checked, root1Node27Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root1Node27Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node27Domains1 (.output 13) = true := by decide
def root1Node28Domains0 : Domains 37 State := restrict root1Node0Domains4 2 (7,5)
def root1Node28Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 1 => some [(0,3),(1,1),(6,1),(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(0,2),(0,3),(6,0)]
  | 4 => some [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 5 => some [(2,0),(2,2),(4,0)]
  | 6 => some [(3,3),(7,3)]
  | 7 => some [(4,2),(5,2),(8,2)]
  | 8 => some [(5,0),(5,3),(8,0)]
  | 9 => some [(0,2),(0,3),(1,1),(6,0),(6,1)]
  | 10 => some [(1,1),(3,1),(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(7,4),(8,4)]
  | 14 => some [(0,0),(1,3),(1,4),(6,3),(6,4)]
  | 15 => some [(4,2),(5,2),(7,0),(8,0),(8,2)]
  | 16 => some [(5,0),(5,3),(8,3)]
  | 17 => some [(4,5),(5,5),(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(2,1),(7,1)]
  | 20 => some [(0,2),(1,5),(6,5),(7,5)]
  | 21 => some [(0,3),(0,4),(1,1),(6,0),(6,1)]
  | 22 => some [(1,4),(7,4),(8,4)]
  | 23 => some [(0,0),(0,5),(1,3),(6,3)]
  | 24 => some [(4,4),(7,2),(8,2)]
  | 25 => some [(0,0),(4,0),(5,0),(8,0)]
  | 26 => some [(3,2),(4,5),(7,3)]
  | 27 => some [(4,0),(4,2),(7,0),(8,2)]
  | 28 => some [(0,2),(1,5),(6,0),(6,5)]
  | 29 => some [(0,4),(1,1),(6,1),(7,1)]
  | 30 => some [(1,5),(5,1),(5,4)]
  | 31 => some [(0,0),(0,1),(6,1),(6,4)]
  | 32 => some [(1,2),(5,1),(6,2),(7,2)]
  | 33 => some [(5,0),(7,0),(8,0)]
  | 34 => some [(4,3),(4,5),(8,3)]
  | 35 => some [(1,5),(3,5),(5,5),(7,0),(7,5),(8,5)]
  | _ => some [(0,3),(1,0),(6,1),(8,3)]
theorem root1Node28Domains0_fast_eq : root1Node28Domains0 = expandDomains root1Node28Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node28Domains0 v = expandDomains root1Node28Domains0Fast v from by decide) v
def root1Node28Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(1,0),(6,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(0,2),(0,3),(6,0)]
  | 4 => [(7,2)]
  | 5 => [(4,0)]
  | 6 => [(7,3)]
  | 7 => [(4,2),(8,2)]
  | 8 => [(5,0),(5,3),(8,0)]
  | 9 => [(1,1),(6,1)]
  | 10 => [(5,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(7,4),(8,4)]
  | 14 => [(0,0),(1,3),(1,4),(6,3),(6,4)]
  | 15 => [(4,2),(5,2),(7,0),(8,0),(8,2)]
  | 16 => [(8,3)]
  | 17 => [(5,5),(8,5)]
  | 18 => [(1,0)]
  | 19 => [(2,1),(7,1)]
  | 20 => [(0,2),(1,5),(6,5),(7,5)]
  | 21 => [(0,3),(0,4),(1,1),(6,0),(6,1)]
  | 22 => [(1,4),(7,4),(8,4)]
  | 23 => [(0,5),(1,3),(6,3)]
  | 24 => [(4,4),(7,2),(8,2)]
  | 25 => [(0,0),(4,0),(5,0),(8,0)]
  | 26 => [(3,2),(4,5),(7,3)]
  | 27 => [(4,0),(4,2),(7,0),(8,2)]
  | 28 => [(0,2),(1,5),(6,0),(6,5)]
  | 29 => [(0,4),(1,1),(6,1),(7,1)]
  | 30 => [(1,5),(5,1),(5,4)]
  | 31 => [(0,0),(0,1),(6,1),(6,4)]
  | 32 => [(1,2),(5,1),(6,2),(7,2)]
  | 33 => [(5,0),(7,0),(8,0)]
  | 34 => [(4,3),(4,5),(8,3)]
  | 35 => [(1,5),(3,5),(5,5),(7,0),(7,5),(8,5)]
  | _ => [(0,3),(1,0),(6,1),(8,3)]
def root1Node28Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0),(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(0,2),(0,3),(6,0)]
  | 4 => some [(7,2)]
  | 5 => some [(4,0)]
  | 6 => some [(7,3)]
  | 7 => some [(4,2),(8,2)]
  | 8 => some [(5,0),(5,3),(8,0)]
  | 9 => some [(1,1),(6,1)]
  | 10 => some [(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(7,4),(8,4)]
  | 14 => some [(0,0),(1,3),(1,4),(6,3),(6,4)]
  | 15 => some [(4,2),(5,2),(7,0),(8,0),(8,2)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5),(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(2,1),(7,1)]
  | 20 => some [(0,2),(1,5),(6,5),(7,5)]
  | 21 => some [(0,3),(0,4),(1,1),(6,0),(6,1)]
  | 22 => some [(1,4),(7,4),(8,4)]
  | 23 => some [(0,5),(1,3),(6,3)]
  | 24 => some [(4,4),(7,2),(8,2)]
  | 25 => some [(0,0),(4,0),(5,0),(8,0)]
  | 26 => some [(3,2),(4,5),(7,3)]
  | 27 => some [(4,0),(4,2),(7,0),(8,2)]
  | 28 => some [(0,2),(1,5),(6,0),(6,5)]
  | 29 => some [(0,4),(1,1),(6,1),(7,1)]
  | 30 => some [(1,5),(5,1),(5,4)]
  | 31 => some [(0,0),(0,1),(6,1),(6,4)]
  | 32 => some [(1,2),(5,1),(6,2),(7,2)]
  | 33 => some [(5,0),(7,0),(8,0)]
  | 34 => some [(4,3),(4,5),(8,3)]
  | 35 => some [(1,5),(3,5),(5,5),(7,0),(7,5),(8,5)]
  | _ => some [(0,3),(1,0),(6,1),(8,3)]
theorem root1Node28Domains1_fast_eq : root1Node28Domains1 = expandDomains root1Node28Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node28Domains1 v = expandDomains root1Node28Domains1Fast v from by decide) v
theorem root1Node28Step1Chunk0_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_0⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk0_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_1⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk0_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_2⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk0_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_3⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk0_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_4⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk0_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_5⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk1_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_0⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk1_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_1⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk1_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_2⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk1_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_3⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk1_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_4⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk1_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_5⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk2_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_0⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk2_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_1⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk2_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_2⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk2_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_3⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk2_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_4⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk2_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_5⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk3_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_0⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk3_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_1⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk3_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_2⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk3_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_3⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk3_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_4⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk3_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_5⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk4_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_0⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk4_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_1⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk4_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_2⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk4_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_3⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk4_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_4⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk4_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_5⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk5_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_0⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk5_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_1⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk5_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_2⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk5_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_3⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk5_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_4⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk5_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_5⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk6_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_0⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk6_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_1⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk6_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_2⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk6_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_3⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk6_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_4⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk6_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_5⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk7_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_0⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk7_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_1⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk7_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_2⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk7_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_3⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk7_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_4⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk7_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_5⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk8_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_0⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk8_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_1⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk8_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_2⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk8_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_3⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk8_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_4⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk8_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_5⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1_checked :
    checkReplacement table11 root1Node28Domains0 root1Node28Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node28Step1Chunk0_0_checked, root1Node28Step1Chunk0_1_checked, root1Node28Step1Chunk0_2_checked, root1Node28Step1Chunk0_3_checked, root1Node28Step1Chunk0_4_checked, root1Node28Step1Chunk0_5_checked, root1Node28Step1Chunk1_0_checked, root1Node28Step1Chunk1_1_checked, root1Node28Step1Chunk1_2_checked, root1Node28Step1Chunk1_3_checked, root1Node28Step1Chunk1_4_checked, root1Node28Step1Chunk1_5_checked, root1Node28Step1Chunk2_0_checked, root1Node28Step1Chunk2_1_checked, root1Node28Step1Chunk2_2_checked, root1Node28Step1Chunk2_3_checked, root1Node28Step1Chunk2_4_checked, root1Node28Step1Chunk2_5_checked, root1Node28Step1Chunk3_0_checked, root1Node28Step1Chunk3_1_checked, root1Node28Step1Chunk3_2_checked, root1Node28Step1Chunk3_3_checked, root1Node28Step1Chunk3_4_checked, root1Node28Step1Chunk3_5_checked, root1Node28Step1Chunk4_0_checked, root1Node28Step1Chunk4_1_checked, root1Node28Step1Chunk4_2_checked, root1Node28Step1Chunk4_3_checked, root1Node28Step1Chunk4_4_checked, root1Node28Step1Chunk4_5_checked, root1Node28Step1Chunk5_0_checked, root1Node28Step1Chunk5_1_checked, root1Node28Step1Chunk5_2_checked, root1Node28Step1Chunk5_3_checked, root1Node28Step1Chunk5_4_checked, root1Node28Step1Chunk5_5_checked, root1Node28Step1Chunk6_0_checked, root1Node28Step1Chunk6_1_checked, root1Node28Step1Chunk6_2_checked, root1Node28Step1Chunk6_3_checked, root1Node28Step1Chunk6_4_checked, root1Node28Step1Chunk6_5_checked, root1Node28Step1Chunk7_0_checked, root1Node28Step1Chunk7_1_checked, root1Node28Step1Chunk7_2_checked, root1Node28Step1Chunk7_3_checked, root1Node28Step1Chunk7_4_checked, root1Node28Step1Chunk7_5_checked, root1Node28Step1Chunk8_0_checked, root1Node28Step1Chunk8_1_checked, root1Node28Step1Chunk8_2_checked, root1Node28Step1Chunk8_3_checked, root1Node28Step1Chunk8_4_checked, root1Node28Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node28Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(1,0),(6,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(0,2),(0,3),(6,0)]
  | 4 => [(7,2)]
  | 5 => [(4,0)]
  | 6 => [(7,3)]
  | 7 => [(4,2),(8,2)]
  | 8 => [(5,0),(5,3),(8,0)]
  | 9 => [(1,1),(6,1)]
  | 10 => [(5,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(7,4),(8,4)]
  | 14 => [(0,0),(1,3),(1,4),(6,3),(6,4)]
  | 15 => [(7,0),(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5),(8,5)]
  | 18 => [(1,0)]
  | 19 => [(2,1),(7,1)]
  | 20 => [(0,2),(1,5),(6,5),(7,5)]
  | 21 => [(0,3),(0,4),(1,1),(6,0),(6,1)]
  | 22 => [(1,4),(7,4)]
  | 23 => [(0,5),(1,3),(6,3)]
  | 24 => [(4,4),(7,2),(8,2)]
  | 25 => [(0,0),(4,0),(5,0),(8,0)]
  | 26 => [(3,2),(4,5),(7,3)]
  | 27 => [(4,0),(4,2),(7,0),(8,2)]
  | 28 => [(0,2),(6,0),(6,5)]
  | 29 => [(0,4),(1,1),(7,1)]
  | 30 => [(1,5),(5,1),(5,4)]
  | 31 => [(0,0),(0,1),(6,1),(6,4)]
  | 32 => [(1,2),(5,1),(6,2),(7,2)]
  | 33 => [(5,0),(7,0),(8,0)]
  | 34 => [(4,3),(4,5),(8,3)]
  | 35 => [(1,5),(3,5),(5,5),(7,0),(7,5),(8,5)]
  | _ => [(0,3),(1,0),(6,1),(8,3)]
def root1Node28Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0),(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(0,2),(0,3),(6,0)]
  | 4 => some [(7,2)]
  | 5 => some [(4,0)]
  | 6 => some [(7,3)]
  | 7 => some [(4,2),(8,2)]
  | 8 => some [(5,0),(5,3),(8,0)]
  | 9 => some [(1,1),(6,1)]
  | 10 => some [(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(7,4),(8,4)]
  | 14 => some [(0,0),(1,3),(1,4),(6,3),(6,4)]
  | 15 => some [(7,0),(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5),(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(2,1),(7,1)]
  | 20 => some [(0,2),(1,5),(6,5),(7,5)]
  | 21 => some [(0,3),(0,4),(1,1),(6,0),(6,1)]
  | 22 => some [(1,4),(7,4)]
  | 23 => some [(0,5),(1,3),(6,3)]
  | 24 => some [(4,4),(7,2),(8,2)]
  | 25 => some [(0,0),(4,0),(5,0),(8,0)]
  | 26 => some [(3,2),(4,5),(7,3)]
  | 27 => some [(4,0),(4,2),(7,0),(8,2)]
  | 28 => some [(0,2),(6,0),(6,5)]
  | 29 => some [(0,4),(1,1),(7,1)]
  | 30 => some [(1,5),(5,1),(5,4)]
  | 31 => some [(0,0),(0,1),(6,1),(6,4)]
  | 32 => some [(1,2),(5,1),(6,2),(7,2)]
  | 33 => some [(5,0),(7,0),(8,0)]
  | 34 => some [(4,3),(4,5),(8,3)]
  | 35 => some [(1,5),(3,5),(5,5),(7,0),(7,5),(8,5)]
  | _ => some [(0,3),(1,0),(6,1),(8,3)]
theorem root1Node28Domains2_fast_eq : root1Node28Domains2 = expandDomains root1Node28Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node28Domains2 v = expandDomains root1Node28Domains2Fast v from by decide) v
theorem root1Node28Step2Chunk0_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_0⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk0_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_1⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk0_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_2⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk0_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_3⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk0_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_4⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk0_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_5⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk1_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_0⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk1_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_1⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk1_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_2⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk1_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_3⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk1_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_4⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk1_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_5⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk2_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_0⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk2_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_1⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk2_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_2⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk2_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_3⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk2_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_4⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk2_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_5⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk3_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_0⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk3_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_1⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk3_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_2⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk3_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_3⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk3_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_4⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk3_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_5⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk4_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_0⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk4_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_1⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk4_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_2⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk4_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_3⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk4_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_4⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk4_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_5⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk5_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_0⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk5_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_1⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk5_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_2⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk5_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_3⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk5_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_4⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk5_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_5⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk6_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_0⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk6_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_1⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk6_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_2⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk6_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_3⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk6_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_4⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk6_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_5⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk7_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_0⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk7_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_1⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk7_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_2⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk7_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_3⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk7_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_4⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk7_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_5⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk8_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_0⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk8_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_1⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk8_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_2⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk8_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_3⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk8_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_4⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2Chunk8_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_5⟩
      root1Node28Domains1 root1Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains1 root1Node28Domains2
    root1Node28Domains1Fast root1Node28Domains2Fast
    root1Node28Domains1_fast_eq root1Node28Domains2_fast_eq (by decide)
theorem root1Node28Step2_checked :
    checkReplacement table16 root1Node28Domains1 root1Node28Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node28Step2Chunk0_0_checked, root1Node28Step2Chunk0_1_checked, root1Node28Step2Chunk0_2_checked, root1Node28Step2Chunk0_3_checked, root1Node28Step2Chunk0_4_checked, root1Node28Step2Chunk0_5_checked, root1Node28Step2Chunk1_0_checked, root1Node28Step2Chunk1_1_checked, root1Node28Step2Chunk1_2_checked, root1Node28Step2Chunk1_3_checked, root1Node28Step2Chunk1_4_checked, root1Node28Step2Chunk1_5_checked, root1Node28Step2Chunk2_0_checked, root1Node28Step2Chunk2_1_checked, root1Node28Step2Chunk2_2_checked, root1Node28Step2Chunk2_3_checked, root1Node28Step2Chunk2_4_checked, root1Node28Step2Chunk2_5_checked, root1Node28Step2Chunk3_0_checked, root1Node28Step2Chunk3_1_checked, root1Node28Step2Chunk3_2_checked, root1Node28Step2Chunk3_3_checked, root1Node28Step2Chunk3_4_checked, root1Node28Step2Chunk3_5_checked, root1Node28Step2Chunk4_0_checked, root1Node28Step2Chunk4_1_checked, root1Node28Step2Chunk4_2_checked, root1Node28Step2Chunk4_3_checked, root1Node28Step2Chunk4_4_checked, root1Node28Step2Chunk4_5_checked, root1Node28Step2Chunk5_0_checked, root1Node28Step2Chunk5_1_checked, root1Node28Step2Chunk5_2_checked, root1Node28Step2Chunk5_3_checked, root1Node28Step2Chunk5_4_checked, root1Node28Step2Chunk5_5_checked, root1Node28Step2Chunk6_0_checked, root1Node28Step2Chunk6_1_checked, root1Node28Step2Chunk6_2_checked, root1Node28Step2Chunk6_3_checked, root1Node28Step2Chunk6_4_checked, root1Node28Step2Chunk6_5_checked, root1Node28Step2Chunk7_0_checked, root1Node28Step2Chunk7_1_checked, root1Node28Step2Chunk7_2_checked, root1Node28Step2Chunk7_3_checked, root1Node28Step2Chunk7_4_checked, root1Node28Step2Chunk7_5_checked, root1Node28Step2Chunk8_0_checked, root1Node28Step2Chunk8_1_checked, root1Node28Step2Chunk8_2_checked, root1Node28Step2Chunk8_3_checked, root1Node28Step2Chunk8_4_checked, root1Node28Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
