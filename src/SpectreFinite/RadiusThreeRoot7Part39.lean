module

public import SpectreFinite.RadiusThreeRoot7Part38
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable22
public import SpectreFinite.RadiusThreeTable25

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node56Domains0 : Domains 37 State := restrict root7Node55Domains1 17 (5,5)
def root7Node56Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(8,2)]
  | 8 => some [(8,0)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(6,4)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(3,5),(7,5)]
  | 21 => some [(0,3)]
  | 22 => some [(1,4),(3,4),(7,4)]
  | 23 => some [(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(7,4)]
  | 26 => some [(0,5),(1,3),(6,3)]
  | 27 => some [(2,2),(2,4),(4,2)]
  | 28 => some [(0,2),(6,0)]
  | 29 => some [(1,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(7,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5),(8,2)]
  | _ => some [(3,0),(5,0),(7,0)]
theorem root7Node56Domains0_fast_eq : root7Node56Domains0 = expandDomains root7Node56Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node56Domains0 v = expandDomains root7Node56Domains0Fast v from by decide) v
def root7Node56Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(8,2)]
  | 8 => [(8,0)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(6,4)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(3,5)]
  | 21 => [(0,3)]
  | 22 => [(1,4),(3,4),(7,4)]
  | 23 => [(0,5)]
  | 24 => [(4,4)]
  | 25 => [(1,4)]
  | 26 => [(0,5)]
  | 27 => [(2,4)]
  | 28 => [(0,2),(6,0)]
  | 29 => [(7,1)]
  | 30 => [(7,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(4,0),(8,0)]
  | 34 => [(7,3)]
  | 35 => [(8,2)]
  | _ => [(5,0)]
def root7Node56Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(8,2)]
  | 8 => some [(8,0)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(6,4)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(3,5)]
  | 21 => some [(0,3)]
  | 22 => some [(1,4),(3,4),(7,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(1,4)]
  | 26 => some [(0,5)]
  | 27 => some [(2,4)]
  | 28 => some [(0,2),(6,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(8,2)]
  | _ => some [(5,0)]
theorem root7Node56Domains1_fast_eq : root7Node56Domains1 = expandDomains root7Node56Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node56Domains1 v = expandDomains root7Node56Domains1Fast v from by decide) v
theorem root7Node56Step1Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root7Node56Domains0 root7Node56Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains0 root7Node56Domains1
    root7Node56Domains0Fast root7Node56Domains1Fast
    root7Node56Domains0_fast_eq root7Node56Domains1_fast_eq (by decide)
theorem root7Node56Step1_checked :
    checkReplacement table25 root7Node56Domains0 root7Node56Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node56Step1Chunk0_0_checked, root7Node56Step1Chunk0_1_checked, root7Node56Step1Chunk0_2_checked, root7Node56Step1Chunk0_3_checked, root7Node56Step1Chunk0_4_checked, root7Node56Step1Chunk0_5_checked, root7Node56Step1Chunk1_0_checked, root7Node56Step1Chunk1_1_checked, root7Node56Step1Chunk1_2_checked, root7Node56Step1Chunk1_3_checked, root7Node56Step1Chunk1_4_checked, root7Node56Step1Chunk1_5_checked, root7Node56Step1Chunk2_0_checked, root7Node56Step1Chunk2_1_checked, root7Node56Step1Chunk2_2_checked, root7Node56Step1Chunk2_3_checked, root7Node56Step1Chunk2_4_checked, root7Node56Step1Chunk2_5_checked, root7Node56Step1Chunk3_0_checked, root7Node56Step1Chunk3_1_checked, root7Node56Step1Chunk3_2_checked, root7Node56Step1Chunk3_3_checked, root7Node56Step1Chunk3_4_checked, root7Node56Step1Chunk3_5_checked, root7Node56Step1Chunk4_0_checked, root7Node56Step1Chunk4_1_checked, root7Node56Step1Chunk4_2_checked, root7Node56Step1Chunk4_3_checked, root7Node56Step1Chunk4_4_checked, root7Node56Step1Chunk4_5_checked, root7Node56Step1Chunk5_0_checked, root7Node56Step1Chunk5_1_checked, root7Node56Step1Chunk5_2_checked, root7Node56Step1Chunk5_3_checked, root7Node56Step1Chunk5_4_checked, root7Node56Step1Chunk5_5_checked, root7Node56Step1Chunk6_0_checked, root7Node56Step1Chunk6_1_checked, root7Node56Step1Chunk6_2_checked, root7Node56Step1Chunk6_3_checked, root7Node56Step1Chunk6_4_checked, root7Node56Step1Chunk6_5_checked, root7Node56Step1Chunk7_0_checked, root7Node56Step1Chunk7_1_checked, root7Node56Step1Chunk7_2_checked, root7Node56Step1Chunk7_3_checked, root7Node56Step1Chunk7_4_checked, root7Node56Step1Chunk7_5_checked, root7Node56Step1Chunk8_0_checked, root7Node56Step1Chunk8_1_checked, root7Node56Step1Chunk8_2_checked, root7Node56Step1Chunk8_3_checked, root7Node56Step1Chunk8_4_checked, root7Node56Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node56Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(8,2)]
  | 8 => [(8,0)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(6,4)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(3,5)]
  | 21 => [(0,3)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(4,4)]
  | 25 => [(1,4)]
  | 26 => [(0,5)]
  | 27 => [(2,4)]
  | 28 => [(6,0)]
  | 29 => [(7,1)]
  | 30 => [(7,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(4,0)]
  | 34 => [(7,3)]
  | 35 => [(8,2)]
  | _ => [(5,0)]
def root7Node56Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(8,2)]
  | 8 => some [(8,0)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(6,4)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(3,5)]
  | 21 => some [(0,3)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(1,4)]
  | 26 => some [(0,5)]
  | 27 => some [(2,4)]
  | 28 => some [(6,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(4,0)]
  | 34 => some [(7,3)]
  | 35 => some [(8,2)]
  | _ => some [(5,0)]
theorem root7Node56Domains2_fast_eq : root7Node56Domains2 = expandDomains root7Node56Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node56Domains2 v = expandDomains root7Node56Domains2Fast v from by decide) v
theorem root7Node56Step2Chunk0_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_0⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk0_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_1⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk0_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_2⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk0_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_3⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk0_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_4⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk0_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_5⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk1_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_0⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk1_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_1⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk1_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_2⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk1_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_3⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk1_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_4⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk1_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_5⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk2_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_0⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk2_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_1⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk2_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_2⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk2_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_3⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk2_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_4⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk2_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_5⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk3_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_0⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk3_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_1⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk3_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_2⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk3_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_3⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk3_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_4⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk3_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_5⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk4_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_0⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk4_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_1⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk4_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_2⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk4_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_3⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk4_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_4⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk4_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_5⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk5_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_0⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk5_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_1⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk5_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_2⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk5_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_3⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk5_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_4⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk5_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_5⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk6_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_0⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk6_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_1⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk6_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_2⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk6_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_3⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk6_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_4⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk6_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_5⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk7_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_0⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk7_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_1⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk7_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_2⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk7_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_3⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk7_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_4⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk7_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_5⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk8_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_0⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk8_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_1⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk8_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_2⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk8_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_3⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk8_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_4⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2Chunk8_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_5⟩
      root7Node56Domains1 root7Node56Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node56Domains1 root7Node56Domains2
    root7Node56Domains1Fast root7Node56Domains2Fast
    root7Node56Domains1_fast_eq root7Node56Domains2_fast_eq (by decide)
theorem root7Node56Step2_checked :
    checkReplacement table22 root7Node56Domains1 root7Node56Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node56Step2Chunk0_0_checked, root7Node56Step2Chunk0_1_checked, root7Node56Step2Chunk0_2_checked, root7Node56Step2Chunk0_3_checked, root7Node56Step2Chunk0_4_checked, root7Node56Step2Chunk0_5_checked, root7Node56Step2Chunk1_0_checked, root7Node56Step2Chunk1_1_checked, root7Node56Step2Chunk1_2_checked, root7Node56Step2Chunk1_3_checked, root7Node56Step2Chunk1_4_checked, root7Node56Step2Chunk1_5_checked, root7Node56Step2Chunk2_0_checked, root7Node56Step2Chunk2_1_checked, root7Node56Step2Chunk2_2_checked, root7Node56Step2Chunk2_3_checked, root7Node56Step2Chunk2_4_checked, root7Node56Step2Chunk2_5_checked, root7Node56Step2Chunk3_0_checked, root7Node56Step2Chunk3_1_checked, root7Node56Step2Chunk3_2_checked, root7Node56Step2Chunk3_3_checked, root7Node56Step2Chunk3_4_checked, root7Node56Step2Chunk3_5_checked, root7Node56Step2Chunk4_0_checked, root7Node56Step2Chunk4_1_checked, root7Node56Step2Chunk4_2_checked, root7Node56Step2Chunk4_3_checked, root7Node56Step2Chunk4_4_checked, root7Node56Step2Chunk4_5_checked, root7Node56Step2Chunk5_0_checked, root7Node56Step2Chunk5_1_checked, root7Node56Step2Chunk5_2_checked, root7Node56Step2Chunk5_3_checked, root7Node56Step2Chunk5_4_checked, root7Node56Step2Chunk5_5_checked, root7Node56Step2Chunk6_0_checked, root7Node56Step2Chunk6_1_checked, root7Node56Step2Chunk6_2_checked, root7Node56Step2Chunk6_3_checked, root7Node56Step2Chunk6_4_checked, root7Node56Step2Chunk6_5_checked, root7Node56Step2Chunk7_0_checked, root7Node56Step2Chunk7_1_checked, root7Node56Step2Chunk7_2_checked, root7Node56Step2Chunk7_3_checked, root7Node56Step2Chunk7_4_checked, root7Node56Step2Chunk7_5_checked, root7Node56Step2Chunk8_0_checked, root7Node56Step2Chunk8_1_checked, root7Node56Step2Chunk8_2_checked, root7Node56Step2Chunk8_3_checked, root7Node56Step2Chunk8_4_checked, root7Node56Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root7Node56Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node56Domains2 (.output 27) = true := by decide
def root7Node57Domains0 : Domains 37 State := restrict root7Node55Domains1 17 (8,5)
def root7Node57Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(8,2)]
  | 8 => some [(8,0)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(6,4)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(3,5),(7,5)]
  | 21 => some [(0,3)]
  | 22 => some [(1,4),(3,4),(7,4)]
  | 23 => some [(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(7,4)]
  | 26 => some [(0,5),(1,3),(6,3)]
  | 27 => some [(2,2),(2,4),(4,2)]
  | 28 => some [(0,2),(6,0)]
  | 29 => some [(1,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(7,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5),(8,2)]
  | _ => some [(3,0),(5,0),(7,0)]
theorem root7Node57Domains0_fast_eq : root7Node57Domains0 = expandDomains root7Node57Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node57Domains0 v = expandDomains root7Node57Domains0Fast v from by decide) v
def root7Node57Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(8,2)]
  | 8 => [(8,0)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(5,4)]
  | 14 => [(6,4)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(0,3)]
  | 22 => [(1,4),(3,4),(7,4)]
  | 23 => [(6,3)]
  | 24 => [(7,2)]
  | 25 => [(7,4)]
  | 26 => [(1,3),(6,3)]
  | 27 => [(2,2),(4,2)]
  | 28 => [(0,2),(6,0)]
  | 29 => [(1,1)]
  | 30 => [(4,1),(8,1)]
  | 31 => [(0,2),(6,5)]
  | 32 => [(0,4),(1,1)]
  | 33 => [(4,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(5,2),(5,5)]
  | _ => [(3,0),(5,0),(7,0)]
def root7Node57Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(8,2)]
  | 8 => some [(8,0)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(5,4)]
  | 14 => some [(6,4)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3)]
  | 22 => some [(1,4),(3,4),(7,4)]
  | 23 => some [(6,3)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(1,3),(6,3)]
  | 27 => some [(2,2),(4,2)]
  | 28 => some [(0,2),(6,0)]
  | 29 => some [(1,1)]
  | 30 => some [(4,1),(8,1)]
  | 31 => some [(0,2),(6,5)]
  | 32 => some [(0,4),(1,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5)]
  | _ => some [(3,0),(5,0),(7,0)]
theorem root7Node57Domains1_fast_eq : root7Node57Domains1 = expandDomains root7Node57Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node57Domains1 v = expandDomains root7Node57Domains1Fast v from by decide) v
theorem root7Node57Step1Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root7Node57Domains0 root7Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node57Domains0 root7Node57Domains1
    root7Node57Domains0Fast root7Node57Domains1Fast
    root7Node57Domains0_fast_eq root7Node57Domains1_fast_eq (by decide)
theorem root7Node57Step1_checked :
    checkReplacement table25 root7Node57Domains0 root7Node57Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node57Step1Chunk0_0_checked, root7Node57Step1Chunk0_1_checked, root7Node57Step1Chunk0_2_checked, root7Node57Step1Chunk0_3_checked, root7Node57Step1Chunk0_4_checked, root7Node57Step1Chunk0_5_checked, root7Node57Step1Chunk1_0_checked, root7Node57Step1Chunk1_1_checked, root7Node57Step1Chunk1_2_checked, root7Node57Step1Chunk1_3_checked, root7Node57Step1Chunk1_4_checked, root7Node57Step1Chunk1_5_checked, root7Node57Step1Chunk2_0_checked, root7Node57Step1Chunk2_1_checked, root7Node57Step1Chunk2_2_checked, root7Node57Step1Chunk2_3_checked, root7Node57Step1Chunk2_4_checked, root7Node57Step1Chunk2_5_checked, root7Node57Step1Chunk3_0_checked, root7Node57Step1Chunk3_1_checked, root7Node57Step1Chunk3_2_checked, root7Node57Step1Chunk3_3_checked, root7Node57Step1Chunk3_4_checked, root7Node57Step1Chunk3_5_checked, root7Node57Step1Chunk4_0_checked, root7Node57Step1Chunk4_1_checked, root7Node57Step1Chunk4_2_checked, root7Node57Step1Chunk4_3_checked, root7Node57Step1Chunk4_4_checked, root7Node57Step1Chunk4_5_checked, root7Node57Step1Chunk5_0_checked, root7Node57Step1Chunk5_1_checked, root7Node57Step1Chunk5_2_checked, root7Node57Step1Chunk5_3_checked, root7Node57Step1Chunk5_4_checked, root7Node57Step1Chunk5_5_checked, root7Node57Step1Chunk6_0_checked, root7Node57Step1Chunk6_1_checked, root7Node57Step1Chunk6_2_checked, root7Node57Step1Chunk6_3_checked, root7Node57Step1Chunk6_4_checked, root7Node57Step1Chunk6_5_checked, root7Node57Step1Chunk7_0_checked, root7Node57Step1Chunk7_1_checked, root7Node57Step1Chunk7_2_checked, root7Node57Step1Chunk7_3_checked, root7Node57Step1Chunk7_4_checked, root7Node57Step1Chunk7_5_checked, root7Node57Step1Chunk8_0_checked, root7Node57Step1Chunk8_1_checked, root7Node57Step1Chunk8_2_checked, root7Node57Step1Chunk8_3_checked, root7Node57Step1Chunk8_4_checked, root7Node57Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
