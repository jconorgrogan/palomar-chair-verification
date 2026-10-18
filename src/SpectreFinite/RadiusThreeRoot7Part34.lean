module

public import SpectreFinite.RadiusThreeRoot7Part33
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable1
public import SpectreFinite.RadiusThreeTable13
public import SpectreFinite.RadiusThreeTable9

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node52Domains0 : Domains 37 State := restrict root7Node44Domains3 5 (7,4)
def root7Node52Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(3,5),(4,2),(7,0)]
  | 1 => some [(0,3),(4,3),(5,3),(8,3)]
  | 2 => some [(4,1),(7,5),(8,5)]
  | 3 => some [(0,2),(0,3),(1,0),(6,0)]
  | 4 => some [(0,5),(1,2),(6,2),(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(4,2),(5,2),(8,2)]
  | 8 => some [(5,0),(5,3),(8,0)]
  | 9 => some [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(3,4),(5,4)]
  | 14 => some [(0,0),(1,4),(6,3),(6,4)]
  | 15 => some [(4,2),(7,0),(8,0),(8,2)]
  | 16 => some [(5,0),(5,3),(8,3)]
  | 17 => some [(4,5),(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3),(4,3)]
  | 20 => some [(0,2),(1,5),(3,5),(7,5)]
  | 21 => some [(0,3),(1,1),(6,0),(6,1)]
  | 22 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 23 => some [(0,0),(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(6,4),(7,4)]
  | 26 => some [(0,5),(1,2),(1,3),(6,3)]
  | 27 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(7,2),(8,2)]
  | 28 => some [(0,2),(1,5),(6,0)]
  | 29 => some [(1,1),(6,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(0,3),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 33 => some [(2,0),(4,0),(7,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | _ => some [(3,0),(5,0),(5,3),(7,0),(8,0)]
theorem root7Node52Domains0_fast_eq : root7Node52Domains0 = expandDomains root7Node52Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node52Domains0 v = expandDomains root7Node52Domains0Fast v from by decide) v
def root7Node52Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2),(7,0)]
  | 1 => [(4,3),(5,3),(8,3)]
  | 2 => [(7,5),(8,5)]
  | 3 => [(0,3),(1,0),(6,0)]
  | 4 => [(1,2),(6,2),(7,2)]
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(4,2),(8,2)]
  | 8 => [(5,0),(5,3),(8,0)]
  | 9 => [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 10 => [(7,1),(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(3,4),(5,4)]
  | 14 => [(0,0),(1,4),(6,3),(6,4)]
  | 15 => [(4,2),(7,0),(8,0),(8,2)]
  | 16 => [(5,0),(5,3),(8,3)]
  | 17 => [(4,5),(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(2,3),(4,3)]
  | 20 => [(0,2),(1,5),(3,5),(7,5)]
  | 21 => [(0,3),(1,1),(6,0),(6,1)]
  | 22 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 23 => [(0,0),(0,5),(6,3)]
  | 24 => [(4,4),(7,2)]
  | 25 => [(1,4),(6,4),(7,4)]
  | 26 => [(0,5),(1,2),(1,3),(6,3)]
  | 27 => [(2,0),(2,2),(2,4),(4,0),(4,2),(7,2),(8,2)]
  | 28 => [(0,2),(1,5),(6,0)]
  | 29 => [(1,1),(6,1),(7,1)]
  | 30 => [(4,1),(7,5),(8,1)]
  | 31 => [(0,2),(0,3),(6,0),(6,5)]
  | 32 => [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 33 => [(2,0),(4,0),(7,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | _ => [(3,0),(5,0),(5,3),(7,0),(8,0)]
def root7Node52Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2),(7,0)]
  | 1 => some [(4,3),(5,3),(8,3)]
  | 2 => some [(7,5),(8,5)]
  | 3 => some [(0,3),(1,0),(6,0)]
  | 4 => some [(1,2),(6,2),(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(4,2),(8,2)]
  | 8 => some [(5,0),(5,3),(8,0)]
  | 9 => some [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(3,4),(5,4)]
  | 14 => some [(0,0),(1,4),(6,3),(6,4)]
  | 15 => some [(4,2),(7,0),(8,0),(8,2)]
  | 16 => some [(5,0),(5,3),(8,3)]
  | 17 => some [(4,5),(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3),(4,3)]
  | 20 => some [(0,2),(1,5),(3,5),(7,5)]
  | 21 => some [(0,3),(1,1),(6,0),(6,1)]
  | 22 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 23 => some [(0,0),(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(6,4),(7,4)]
  | 26 => some [(0,5),(1,2),(1,3),(6,3)]
  | 27 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(7,2),(8,2)]
  | 28 => some [(0,2),(1,5),(6,0)]
  | 29 => some [(1,1),(6,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(0,3),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 33 => some [(2,0),(4,0),(7,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | _ => some [(3,0),(5,0),(5,3),(7,0),(8,0)]
theorem root7Node52Domains1_fast_eq : root7Node52Domains1 = expandDomains root7Node52Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node52Domains1 v = expandDomains root7Node52Domains1Fast v from by decide) v
theorem root7Node52Step1Chunk0_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_0⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk0_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_1⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk0_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_2⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk0_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_3⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk0_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_4⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk0_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_5⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk1_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_0⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk1_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_1⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk1_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_2⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk1_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_3⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk1_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_4⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk1_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_5⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk2_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_0⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk2_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_1⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk2_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_2⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk2_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_3⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk2_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_4⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk2_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_5⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk3_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_0⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk3_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_1⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk3_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_2⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk3_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_3⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk3_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_4⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk3_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_5⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk4_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_0⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk4_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_1⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk4_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_2⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk4_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_3⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk4_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_4⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk4_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_5⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk5_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_0⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk5_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_1⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk5_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_2⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk5_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_3⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk5_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_4⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk5_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_5⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk6_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_0⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk6_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_1⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk6_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_2⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk6_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_3⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk6_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_4⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk6_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_5⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk7_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_0⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk7_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_1⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk7_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_2⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk7_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_3⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk7_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_4⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk7_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_5⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk8_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_0⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk8_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_1⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk8_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_2⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk8_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_3⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk8_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_4⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1Chunk8_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_5⟩
      root7Node52Domains0 root7Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains0 root7Node52Domains1
    root7Node52Domains0Fast root7Node52Domains1Fast
    root7Node52Domains0_fast_eq root7Node52Domains1_fast_eq (by decide)
theorem root7Node52Step1_checked :
    checkReplacement table1 root7Node52Domains0 root7Node52Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node52Step1Chunk0_0_checked, root7Node52Step1Chunk0_1_checked, root7Node52Step1Chunk0_2_checked, root7Node52Step1Chunk0_3_checked, root7Node52Step1Chunk0_4_checked, root7Node52Step1Chunk0_5_checked, root7Node52Step1Chunk1_0_checked, root7Node52Step1Chunk1_1_checked, root7Node52Step1Chunk1_2_checked, root7Node52Step1Chunk1_3_checked, root7Node52Step1Chunk1_4_checked, root7Node52Step1Chunk1_5_checked, root7Node52Step1Chunk2_0_checked, root7Node52Step1Chunk2_1_checked, root7Node52Step1Chunk2_2_checked, root7Node52Step1Chunk2_3_checked, root7Node52Step1Chunk2_4_checked, root7Node52Step1Chunk2_5_checked, root7Node52Step1Chunk3_0_checked, root7Node52Step1Chunk3_1_checked, root7Node52Step1Chunk3_2_checked, root7Node52Step1Chunk3_3_checked, root7Node52Step1Chunk3_4_checked, root7Node52Step1Chunk3_5_checked, root7Node52Step1Chunk4_0_checked, root7Node52Step1Chunk4_1_checked, root7Node52Step1Chunk4_2_checked, root7Node52Step1Chunk4_3_checked, root7Node52Step1Chunk4_4_checked, root7Node52Step1Chunk4_5_checked, root7Node52Step1Chunk5_0_checked, root7Node52Step1Chunk5_1_checked, root7Node52Step1Chunk5_2_checked, root7Node52Step1Chunk5_3_checked, root7Node52Step1Chunk5_4_checked, root7Node52Step1Chunk5_5_checked, root7Node52Step1Chunk6_0_checked, root7Node52Step1Chunk6_1_checked, root7Node52Step1Chunk6_2_checked, root7Node52Step1Chunk6_3_checked, root7Node52Step1Chunk6_4_checked, root7Node52Step1Chunk6_5_checked, root7Node52Step1Chunk7_0_checked, root7Node52Step1Chunk7_1_checked, root7Node52Step1Chunk7_2_checked, root7Node52Step1Chunk7_3_checked, root7Node52Step1Chunk7_4_checked, root7Node52Step1Chunk7_5_checked, root7Node52Step1Chunk8_0_checked, root7Node52Step1Chunk8_1_checked, root7Node52Step1Chunk8_2_checked, root7Node52Step1Chunk8_3_checked, root7Node52Step1Chunk8_4_checked, root7Node52Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node52Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2),(7,0)]
  | 1 => [(4,3),(5,3),(8,3)]
  | 2 => [(7,5),(8,5)]
  | 3 => [(0,3),(1,0),(6,0)]
  | 4 => [(1,2),(6,2),(7,2)]
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(4,2),(8,2)]
  | 8 => [(5,0),(5,3),(8,0)]
  | 9 => [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 10 => [(7,1),(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(3,4),(5,4)]
  | 14 => [(0,0),(6,3),(6,4)]
  | 15 => [(4,2),(7,0),(8,0),(8,2)]
  | 16 => [(5,0),(5,3),(8,3)]
  | 17 => [(4,5),(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(2,3),(4,3)]
  | 20 => [(0,2),(1,5),(3,5),(7,5)]
  | 21 => [(0,3),(1,1),(6,1)]
  | 22 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 23 => [(0,0),(0,5),(6,3)]
  | 24 => [(4,4),(7,2)]
  | 25 => [(1,4),(6,4),(7,4)]
  | 26 => [(0,5),(1,2),(1,3),(6,3)]
  | 27 => [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 28 => [(0,2),(1,5),(6,0)]
  | 29 => [(1,1),(6,1),(7,1)]
  | 30 => [(4,1),(7,5),(8,1)]
  | 31 => [(0,2),(0,3),(6,0),(6,5)]
  | 32 => [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 33 => [(2,0),(4,0),(7,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | _ => [(3,0),(5,0),(5,3),(7,0),(8,0)]
def root7Node52Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2),(7,0)]
  | 1 => some [(4,3),(5,3),(8,3)]
  | 2 => some [(7,5),(8,5)]
  | 3 => some [(0,3),(1,0),(6,0)]
  | 4 => some [(1,2),(6,2),(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(4,2),(8,2)]
  | 8 => some [(5,0),(5,3),(8,0)]
  | 9 => some [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(3,4),(5,4)]
  | 14 => some [(0,0),(6,3),(6,4)]
  | 15 => some [(4,2),(7,0),(8,0),(8,2)]
  | 16 => some [(5,0),(5,3),(8,3)]
  | 17 => some [(4,5),(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3),(4,3)]
  | 20 => some [(0,2),(1,5),(3,5),(7,5)]
  | 21 => some [(0,3),(1,1),(6,1)]
  | 22 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 23 => some [(0,0),(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(6,4),(7,4)]
  | 26 => some [(0,5),(1,2),(1,3),(6,3)]
  | 27 => some [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 28 => some [(0,2),(1,5),(6,0)]
  | 29 => some [(1,1),(6,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(0,3),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 33 => some [(2,0),(4,0),(7,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | _ => some [(3,0),(5,0),(5,3),(7,0),(8,0)]
theorem root7Node52Domains2_fast_eq : root7Node52Domains2 = expandDomains root7Node52Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node52Domains2 v = expandDomains root7Node52Domains2Fast v from by decide) v
theorem root7Node52Step2Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root7Node52Domains1 root7Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains1 root7Node52Domains2
    root7Node52Domains1Fast root7Node52Domains2Fast
    root7Node52Domains1_fast_eq root7Node52Domains2_fast_eq (by decide)
theorem root7Node52Step2_checked :
    checkReplacement table13 root7Node52Domains1 root7Node52Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node52Step2Chunk0_0_checked, root7Node52Step2Chunk0_1_checked, root7Node52Step2Chunk0_2_checked, root7Node52Step2Chunk0_3_checked, root7Node52Step2Chunk0_4_checked, root7Node52Step2Chunk0_5_checked, root7Node52Step2Chunk1_0_checked, root7Node52Step2Chunk1_1_checked, root7Node52Step2Chunk1_2_checked, root7Node52Step2Chunk1_3_checked, root7Node52Step2Chunk1_4_checked, root7Node52Step2Chunk1_5_checked, root7Node52Step2Chunk2_0_checked, root7Node52Step2Chunk2_1_checked, root7Node52Step2Chunk2_2_checked, root7Node52Step2Chunk2_3_checked, root7Node52Step2Chunk2_4_checked, root7Node52Step2Chunk2_5_checked, root7Node52Step2Chunk3_0_checked, root7Node52Step2Chunk3_1_checked, root7Node52Step2Chunk3_2_checked, root7Node52Step2Chunk3_3_checked, root7Node52Step2Chunk3_4_checked, root7Node52Step2Chunk3_5_checked, root7Node52Step2Chunk4_0_checked, root7Node52Step2Chunk4_1_checked, root7Node52Step2Chunk4_2_checked, root7Node52Step2Chunk4_3_checked, root7Node52Step2Chunk4_4_checked, root7Node52Step2Chunk4_5_checked, root7Node52Step2Chunk5_0_checked, root7Node52Step2Chunk5_1_checked, root7Node52Step2Chunk5_2_checked, root7Node52Step2Chunk5_3_checked, root7Node52Step2Chunk5_4_checked, root7Node52Step2Chunk5_5_checked, root7Node52Step2Chunk6_0_checked, root7Node52Step2Chunk6_1_checked, root7Node52Step2Chunk6_2_checked, root7Node52Step2Chunk6_3_checked, root7Node52Step2Chunk6_4_checked, root7Node52Step2Chunk6_5_checked, root7Node52Step2Chunk7_0_checked, root7Node52Step2Chunk7_1_checked, root7Node52Step2Chunk7_2_checked, root7Node52Step2Chunk7_3_checked, root7Node52Step2Chunk7_4_checked, root7Node52Step2Chunk7_5_checked, root7Node52Step2Chunk8_0_checked, root7Node52Step2Chunk8_1_checked, root7Node52Step2Chunk8_2_checked, root7Node52Step2Chunk8_3_checked, root7Node52Step2Chunk8_4_checked, root7Node52Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node52Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,2),(7,0)]
  | 1 => [(4,3),(5,3),(8,3)]
  | 2 => [(7,5),(8,5)]
  | 3 => [(0,3),(1,0),(6,0)]
  | 4 => [(1,2),(6,2),(7,2)]
  | 5 => [(7,4)]
  | 6 => [(1,3)]
  | 7 => [(4,2),(8,2)]
  | 8 => [(5,0),(5,3),(8,0)]
  | 9 => [(0,3),(1,0),(1,1),(6,1)]
  | 10 => [(7,1),(8,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(3,4),(5,4)]
  | 14 => [(0,0),(6,3),(6,4)]
  | 15 => [(4,2),(7,0),(8,0),(8,2)]
  | 16 => [(5,0),(5,3),(8,3)]
  | 17 => [(4,5),(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(2,3),(4,3)]
  | 20 => [(0,2),(1,5),(3,5),(7,5)]
  | 21 => [(0,3),(1,1),(6,1)]
  | 22 => [(1,4),(3,4),(5,4),(7,4)]
  | 23 => [(0,0),(0,5),(6,3)]
  | 24 => [(4,4),(7,2)]
  | 25 => [(1,4),(6,4),(7,4)]
  | 26 => [(0,5),(1,2),(1,3),(6,3)]
  | 27 => [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 28 => [(0,2),(1,5),(6,0)]
  | 29 => [(1,1),(6,1),(7,1)]
  | 30 => [(4,1),(7,5),(8,1)]
  | 31 => [(0,2),(0,3),(6,0),(6,5)]
  | 32 => [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 33 => [(2,0),(4,0),(7,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | _ => [(3,0),(5,0),(5,3),(7,0),(8,0)]
def root7Node52Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2),(7,0)]
  | 1 => some [(4,3),(5,3),(8,3)]
  | 2 => some [(7,5),(8,5)]
  | 3 => some [(0,3),(1,0),(6,0)]
  | 4 => some [(1,2),(6,2),(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(1,3)]
  | 7 => some [(4,2),(8,2)]
  | 8 => some [(5,0),(5,3),(8,0)]
  | 9 => some [(0,3),(1,0),(1,1),(6,1)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(3,4),(5,4)]
  | 14 => some [(0,0),(6,3),(6,4)]
  | 15 => some [(4,2),(7,0),(8,0),(8,2)]
  | 16 => some [(5,0),(5,3),(8,3)]
  | 17 => some [(4,5),(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3),(4,3)]
  | 20 => some [(0,2),(1,5),(3,5),(7,5)]
  | 21 => some [(0,3),(1,1),(6,1)]
  | 22 => some [(1,4),(3,4),(5,4),(7,4)]
  | 23 => some [(0,0),(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(6,4),(7,4)]
  | 26 => some [(0,5),(1,2),(1,3),(6,3)]
  | 27 => some [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 28 => some [(0,2),(1,5),(6,0)]
  | 29 => some [(1,1),(6,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(0,3),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 33 => some [(2,0),(4,0),(7,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | _ => some [(3,0),(5,0),(5,3),(7,0),(8,0)]
theorem root7Node52Domains3_fast_eq : root7Node52Domains3 = expandDomains root7Node52Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node52Domains3 v = expandDomains root7Node52Domains3Fast v from by decide) v
theorem root7Node52Step3Chunk0_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_0⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk0_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_1⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk0_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_2⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk0_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_3⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk0_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_4⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk0_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows0_5⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk1_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_0⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk1_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_1⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk1_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_2⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk1_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_3⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk1_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_4⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk1_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows1_5⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk2_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_0⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk2_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_1⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk2_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_2⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk2_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_3⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk2_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_4⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk2_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows2_5⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk3_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_0⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk3_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_1⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk3_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_2⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk3_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_3⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk3_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_4⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk3_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows3_5⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk4_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_0⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk4_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_1⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk4_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_2⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk4_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_3⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk4_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_4⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk4_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows4_5⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk5_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_0⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk5_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_1⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk5_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_2⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk5_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_3⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk5_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_4⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk5_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows5_5⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk6_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_0⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk6_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_1⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk6_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_2⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk6_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_3⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk6_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_4⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk6_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows6_5⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk7_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_0⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk7_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_1⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk7_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_2⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk7_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_3⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk7_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_4⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk7_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows7_5⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk8_0_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_0⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk8_1_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_1⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk8_2_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_2⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk8_3_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_3⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk8_4_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_4⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3Chunk8_5_checked :
    checkNarrowing ⟨table9Scope, table9Rows8_5⟩
      root7Node52Domains2 root7Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node52Domains2 root7Node52Domains3
    root7Node52Domains2Fast root7Node52Domains3Fast
    root7Node52Domains2_fast_eq root7Node52Domains3_fast_eq (by decide)
theorem root7Node52Step3_checked :
    checkReplacement table9 root7Node52Domains2 root7Node52Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node52Step3Chunk0_0_checked, root7Node52Step3Chunk0_1_checked, root7Node52Step3Chunk0_2_checked, root7Node52Step3Chunk0_3_checked, root7Node52Step3Chunk0_4_checked, root7Node52Step3Chunk0_5_checked, root7Node52Step3Chunk1_0_checked, root7Node52Step3Chunk1_1_checked, root7Node52Step3Chunk1_2_checked, root7Node52Step3Chunk1_3_checked, root7Node52Step3Chunk1_4_checked, root7Node52Step3Chunk1_5_checked, root7Node52Step3Chunk2_0_checked, root7Node52Step3Chunk2_1_checked, root7Node52Step3Chunk2_2_checked, root7Node52Step3Chunk2_3_checked, root7Node52Step3Chunk2_4_checked, root7Node52Step3Chunk2_5_checked, root7Node52Step3Chunk3_0_checked, root7Node52Step3Chunk3_1_checked, root7Node52Step3Chunk3_2_checked, root7Node52Step3Chunk3_3_checked, root7Node52Step3Chunk3_4_checked, root7Node52Step3Chunk3_5_checked, root7Node52Step3Chunk4_0_checked, root7Node52Step3Chunk4_1_checked, root7Node52Step3Chunk4_2_checked, root7Node52Step3Chunk4_3_checked, root7Node52Step3Chunk4_4_checked, root7Node52Step3Chunk4_5_checked, root7Node52Step3Chunk5_0_checked, root7Node52Step3Chunk5_1_checked, root7Node52Step3Chunk5_2_checked, root7Node52Step3Chunk5_3_checked, root7Node52Step3Chunk5_4_checked, root7Node52Step3Chunk5_5_checked, root7Node52Step3Chunk6_0_checked, root7Node52Step3Chunk6_1_checked, root7Node52Step3Chunk6_2_checked, root7Node52Step3Chunk6_3_checked, root7Node52Step3Chunk6_4_checked, root7Node52Step3Chunk6_5_checked, root7Node52Step3Chunk7_0_checked, root7Node52Step3Chunk7_1_checked, root7Node52Step3Chunk7_2_checked, root7Node52Step3Chunk7_3_checked, root7Node52Step3Chunk7_4_checked, root7Node52Step3Chunk7_5_checked, root7Node52Step3Chunk8_0_checked, root7Node52Step3Chunk8_1_checked, root7Node52Step3Chunk8_2_checked, root7Node52Step3Chunk8_3_checked, root7Node52Step3Chunk8_4_checked, root7Node52Step3Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
