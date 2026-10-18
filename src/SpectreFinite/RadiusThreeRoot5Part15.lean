module

public import SpectreFinite.RadiusThreeRoot5Part14
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable23

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node26Domains0 : Domains 37 State := restrict root5Node24Domains1 15 (8,0)
def root5Node26Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(2,2)]
  | 8 => some [(3,3)]
  | 9 => some [(1,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0)]
  | 21 => some [(7,1)]
  | 22 => some [(0,1),(6,4)]
  | 23 => some [(1,2),(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(0,3),(1,0)]
  | 29 => some [(7,1),(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(5,1)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(5,5),(8,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root5Node26Domains0_fast_eq : root5Node26Domains0 = expandDomains root5Node26Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node26Domains0 v = expandDomains root5Node26Domains0Fast v from by decide) v
def root5Node26Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(7,2)]
  | 5 => [(7,4)]
  | 6 => [(6,3)]
  | 7 => [(2,2)]
  | 8 => [(3,3)]
  | 9 => [(1,1)]
  | 10 => [(4,1)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(5,0)]
  | 19 => [(4,5)]
  | 20 => [(1,0)]
  | 21 => [(7,1)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(0,3)]
  | 29 => [(8,1)]
  | 30 => [(1,5)]
  | 31 => [(6,1)]
  | 32 => [(5,1)]
  | 33 => [(5,3)]
  | 34 => [(5,5),(8,5)]
  | 35 => [(7,0)]
  | _ => [(8,3)]
def root5Node26Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(2,2)]
  | 8 => some [(3,3)]
  | 9 => some [(1,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0)]
  | 21 => some [(7,1)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(0,3)]
  | 29 => some [(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(5,1)]
  | 33 => some [(5,3)]
  | 34 => some [(5,5),(8,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root5Node26Domains1_fast_eq : root5Node26Domains1 = expandDomains root5Node26Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node26Domains1 v = expandDomains root5Node26Domains1Fast v from by decide) v
theorem root5Node26Step1Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1_checked :
    checkReplacement table23 root5Node26Domains0 root5Node26Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node26Step1Chunk0_0_checked, root5Node26Step1Chunk0_1_checked, root5Node26Step1Chunk0_2_checked, root5Node26Step1Chunk0_3_checked, root5Node26Step1Chunk0_4_checked, root5Node26Step1Chunk0_5_checked, root5Node26Step1Chunk1_0_checked, root5Node26Step1Chunk1_1_checked, root5Node26Step1Chunk1_2_checked, root5Node26Step1Chunk1_3_checked, root5Node26Step1Chunk1_4_checked, root5Node26Step1Chunk1_5_checked, root5Node26Step1Chunk2_0_checked, root5Node26Step1Chunk2_1_checked, root5Node26Step1Chunk2_2_checked, root5Node26Step1Chunk2_3_checked, root5Node26Step1Chunk2_4_checked, root5Node26Step1Chunk2_5_checked, root5Node26Step1Chunk3_0_checked, root5Node26Step1Chunk3_1_checked, root5Node26Step1Chunk3_2_checked, root5Node26Step1Chunk3_3_checked, root5Node26Step1Chunk3_4_checked, root5Node26Step1Chunk3_5_checked, root5Node26Step1Chunk4_0_checked, root5Node26Step1Chunk4_1_checked, root5Node26Step1Chunk4_2_checked, root5Node26Step1Chunk4_3_checked, root5Node26Step1Chunk4_4_checked, root5Node26Step1Chunk4_5_checked, root5Node26Step1Chunk5_0_checked, root5Node26Step1Chunk5_1_checked, root5Node26Step1Chunk5_2_checked, root5Node26Step1Chunk5_3_checked, root5Node26Step1Chunk5_4_checked, root5Node26Step1Chunk5_5_checked, root5Node26Step1Chunk6_0_checked, root5Node26Step1Chunk6_1_checked, root5Node26Step1Chunk6_2_checked, root5Node26Step1Chunk6_3_checked, root5Node26Step1Chunk6_4_checked, root5Node26Step1Chunk6_5_checked, root5Node26Step1Chunk7_0_checked, root5Node26Step1Chunk7_1_checked, root5Node26Step1Chunk7_2_checked, root5Node26Step1Chunk7_3_checked, root5Node26Step1Chunk7_4_checked, root5Node26Step1Chunk7_5_checked, root5Node26Step1Chunk8_0_checked, root5Node26Step1Chunk8_1_checked, root5Node26Step1Chunk8_2_checked, root5Node26Step1Chunk8_3_checked, root5Node26Step1Chunk8_4_checked, root5Node26Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node27Domains0 : Domains 37 State := restrict root5Node26Domains1 34 (5,5)
def root5Node27Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(2,2)]
  | 8 => some [(3,3)]
  | 9 => some [(1,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0)]
  | 21 => some [(7,1)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(0,3)]
  | 29 => some [(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(5,1)]
  | 33 => some [(5,3)]
  | 34 => some [(5,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root5Node27Domains0_fast_eq : root5Node27Domains0 = expandDomains root5Node27Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node27Domains0 v = expandDomains root5Node27Domains0Fast v from by decide) v
theorem root5Node27Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node27Domains0 (.output 11) = true := by decide
def root5Node28Domains0 : Domains 37 State := restrict root5Node26Domains1 34 (8,5)
def root5Node28Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(2,2)]
  | 8 => some [(3,3)]
  | 9 => some [(1,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(5,0)]
  | 19 => some [(4,5)]
  | 20 => some [(1,0)]
  | 21 => some [(7,1)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(0,3)]
  | 29 => some [(8,1)]
  | 30 => some [(1,5)]
  | 31 => some [(6,1)]
  | 32 => some [(5,1)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(7,0)]
  | _ => some [(8,3)]
theorem root5Node28Domains0_fast_eq : root5Node28Domains0 = expandDomains root5Node28Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root5Node28Domains0 v = expandDomains root5Node28Domains0Fast v from by decide) v
theorem root5Node28Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node28Domains0 (.output 12) = true := by decide
end SpectreFinite.HexSearch.RadiusThree
