module

public import SpectreFinite.RadiusThreeRoot6Part7
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable19
public import SpectreFinite.RadiusThreeTable2
public import SpectreFinite.RadiusThreeTable30

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node13Domains0 : Domains 37 State := restrict root6Node7Domains3 2 (8,1)
def root6Node13Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(0,1),(6,5)]
  | 4 => some [(5,2)]
  | 5 => some [(8,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(1,0),(3,0),(7,0)]
  | 9 => some [(0,4),(6,2)]
  | 10 => some [(5,4),(8,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(0,0),(1,4),(6,4)]
  | 15 => some [(1,0),(7,0)]
  | 16 => some [(4,3),(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(0,3),(6,0),(6,1)]
  | 22 => some [(4,0),(7,4),(8,0)]
  | 23 => some [(1,3),(6,3),(7,3)]
  | 24 => some [(7,2),(8,2)]
  | 25 => some [(4,0),(5,0),(8,0)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(4,2),(7,0),(8,2)]
  | 28 => some [(0,1),(0,2),(6,4),(6,5)]
  | 29 => some [(0,4),(1,1),(1,2),(6,2)]
  | 30 => some [(5,1),(5,4),(8,4)]
  | 31 => some [(0,0),(0,1),(6,4)]
  | 32 => some [(1,2),(6,2),(7,2)]
  | 33 => some [(0,3),(1,0),(7,0),(8,0)]
  | 34 => some [(4,3),(7,1),(8,1),(8,3)]
  | 35 => some [(1,5),(3,5),(5,5),(7,5)]
  | _ => some [(0,3),(1,0),(6,1)]
theorem root6Node13Domains0_fast_eq : root6Node13Domains0 = expandDomains root6Node13Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node13Domains0 v = expandDomains root6Node13Domains0Fast v from by decide) v
def root6Node13Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(5,2)]
  | 5 => [(8,0)]
  | 6 => [(8,3)]
  | 7 => [(5,5)]
  | 8 => [(3,0),(7,0)]
  | 9 => [(0,4),(6,2)]
  | 10 => [(5,4),(8,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0),(1,4),(6,4)]
  | 15 => [(1,0),(7,0)]
  | 16 => [(4,3),(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5),(7,5)]
  | 21 => [(0,3),(6,0),(6,1)]
  | 22 => [(4,0),(7,4),(8,0)]
  | 23 => [(1,3),(6,3),(7,3)]
  | 24 => [(7,2),(8,2)]
  | 25 => [(4,0),(5,0),(8,0)]
  | 26 => [(4,5),(7,3)]
  | 27 => [(4,2),(7,0),(8,2)]
  | 28 => [(0,1),(0,2),(6,4),(6,5)]
  | 29 => [(0,4),(1,1),(1,2),(6,2)]
  | 30 => [(5,1),(5,4),(8,4)]
  | 31 => [(0,0),(0,1),(6,4)]
  | 32 => [(1,2),(6,2),(7,2)]
  | 33 => [(0,3),(1,0),(7,0),(8,0)]
  | 34 => [(4,3),(7,1),(8,1),(8,3)]
  | 35 => [(1,5),(3,5),(5,5),(7,5)]
  | _ => [(0,3),(1,0),(6,1)]
def root6Node13Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(5,2)]
  | 5 => some [(8,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(3,0),(7,0)]
  | 9 => some [(0,4),(6,2)]
  | 10 => some [(5,4),(8,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(0,0),(1,4),(6,4)]
  | 15 => some [(1,0),(7,0)]
  | 16 => some [(4,3),(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(0,3),(6,0),(6,1)]
  | 22 => some [(4,0),(7,4),(8,0)]
  | 23 => some [(1,3),(6,3),(7,3)]
  | 24 => some [(7,2),(8,2)]
  | 25 => some [(4,0),(5,0),(8,0)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(4,2),(7,0),(8,2)]
  | 28 => some [(0,1),(0,2),(6,4),(6,5)]
  | 29 => some [(0,4),(1,1),(1,2),(6,2)]
  | 30 => some [(5,1),(5,4),(8,4)]
  | 31 => some [(0,0),(0,1),(6,4)]
  | 32 => some [(1,2),(6,2),(7,2)]
  | 33 => some [(0,3),(1,0),(7,0),(8,0)]
  | 34 => some [(4,3),(7,1),(8,1),(8,3)]
  | 35 => some [(1,5),(3,5),(5,5),(7,5)]
  | _ => some [(0,3),(1,0),(6,1)]
theorem root6Node13Domains1_fast_eq : root6Node13Domains1 = expandDomains root6Node13Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node13Domains1 v = expandDomains root6Node13Domains1Fast v from by decide) v
theorem root6Node13Step1Chunk0_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_0⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk0_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_1⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk0_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_2⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk0_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_3⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk0_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_4⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk0_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_5⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk1_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_0⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk1_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_1⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk1_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_2⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk1_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_3⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk1_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_4⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk1_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_5⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk2_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_0⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk2_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_1⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk2_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_2⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk2_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_3⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk2_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_4⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk2_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_5⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk3_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_0⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk3_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_1⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk3_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_2⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk3_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_3⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk3_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_4⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk3_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_5⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk4_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_0⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk4_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_1⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk4_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_2⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk4_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_3⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk4_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_4⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk4_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_5⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk5_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_0⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk5_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_1⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk5_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_2⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk5_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_3⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk5_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_4⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk5_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_5⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk6_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_0⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk6_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_1⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk6_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_2⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk6_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_3⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk6_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_4⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk6_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_5⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk7_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_0⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk7_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_1⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk7_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_2⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk7_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_3⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk7_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_4⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk7_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_5⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk8_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_0⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk8_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_1⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk8_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_2⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk8_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_3⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk8_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_4⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1Chunk8_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_5⟩
      root6Node13Domains0 root6Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node13Domains0 root6Node13Domains1
    root6Node13Domains0Fast root6Node13Domains1Fast
    root6Node13Domains0_fast_eq root6Node13Domains1_fast_eq (by decide)
theorem root6Node13Step1_checked :
    checkReplacement table2 root6Node13Domains0 root6Node13Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node13Step1Chunk0_0_checked, root6Node13Step1Chunk0_1_checked, root6Node13Step1Chunk0_2_checked, root6Node13Step1Chunk0_3_checked, root6Node13Step1Chunk0_4_checked, root6Node13Step1Chunk0_5_checked, root6Node13Step1Chunk1_0_checked, root6Node13Step1Chunk1_1_checked, root6Node13Step1Chunk1_2_checked, root6Node13Step1Chunk1_3_checked, root6Node13Step1Chunk1_4_checked, root6Node13Step1Chunk1_5_checked, root6Node13Step1Chunk2_0_checked, root6Node13Step1Chunk2_1_checked, root6Node13Step1Chunk2_2_checked, root6Node13Step1Chunk2_3_checked, root6Node13Step1Chunk2_4_checked, root6Node13Step1Chunk2_5_checked, root6Node13Step1Chunk3_0_checked, root6Node13Step1Chunk3_1_checked, root6Node13Step1Chunk3_2_checked, root6Node13Step1Chunk3_3_checked, root6Node13Step1Chunk3_4_checked, root6Node13Step1Chunk3_5_checked, root6Node13Step1Chunk4_0_checked, root6Node13Step1Chunk4_1_checked, root6Node13Step1Chunk4_2_checked, root6Node13Step1Chunk4_3_checked, root6Node13Step1Chunk4_4_checked, root6Node13Step1Chunk4_5_checked, root6Node13Step1Chunk5_0_checked, root6Node13Step1Chunk5_1_checked, root6Node13Step1Chunk5_2_checked, root6Node13Step1Chunk5_3_checked, root6Node13Step1Chunk5_4_checked, root6Node13Step1Chunk5_5_checked, root6Node13Step1Chunk6_0_checked, root6Node13Step1Chunk6_1_checked, root6Node13Step1Chunk6_2_checked, root6Node13Step1Chunk6_3_checked, root6Node13Step1Chunk6_4_checked, root6Node13Step1Chunk6_5_checked, root6Node13Step1Chunk7_0_checked, root6Node13Step1Chunk7_1_checked, root6Node13Step1Chunk7_2_checked, root6Node13Step1Chunk7_3_checked, root6Node13Step1Chunk7_4_checked, root6Node13Step1Chunk7_5_checked, root6Node13Step1Chunk8_0_checked, root6Node13Step1Chunk8_1_checked, root6Node13Step1Chunk8_2_checked, root6Node13Step1Chunk8_3_checked, root6Node13Step1Chunk8_4_checked, root6Node13Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node14Domains0 : Domains 37 State := restrict root6Node13Domains1 8 (3,0)
def root6Node14Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(5,2)]
  | 5 => some [(8,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(3,0)]
  | 9 => some [(0,4),(6,2)]
  | 10 => some [(5,4),(8,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(0,0),(1,4),(6,4)]
  | 15 => some [(1,0),(7,0)]
  | 16 => some [(4,3),(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(0,3),(6,0),(6,1)]
  | 22 => some [(4,0),(7,4),(8,0)]
  | 23 => some [(1,3),(6,3),(7,3)]
  | 24 => some [(7,2),(8,2)]
  | 25 => some [(4,0),(5,0),(8,0)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(4,2),(7,0),(8,2)]
  | 28 => some [(0,1),(0,2),(6,4),(6,5)]
  | 29 => some [(0,4),(1,1),(1,2),(6,2)]
  | 30 => some [(5,1),(5,4),(8,4)]
  | 31 => some [(0,0),(0,1),(6,4)]
  | 32 => some [(1,2),(6,2),(7,2)]
  | 33 => some [(0,3),(1,0),(7,0),(8,0)]
  | 34 => some [(4,3),(7,1),(8,1),(8,3)]
  | 35 => some [(1,5),(3,5),(5,5),(7,5)]
  | _ => some [(0,3),(1,0),(6,1)]
theorem root6Node14Domains0_fast_eq : root6Node14Domains0 = expandDomains root6Node14Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node14Domains0 v = expandDomains root6Node14Domains0Fast v from by decide) v
def root6Node14Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(5,2)]
  | 5 => [(8,0)]
  | 6 => [(8,3)]
  | 7 => [(5,5)]
  | 8 => [(3,0)]
  | 9 => [(0,4),(6,2)]
  | 10 => [(5,4),(8,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0)]
  | 15 => [(1,0),(7,0)]
  | 16 => [(4,3),(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5)]
  | 21 => [(6,1)]
  | 22 => [(4,0),(7,4),(8,0)]
  | 23 => [(1,3),(6,3),(7,3)]
  | 24 => [(8,2)]
  | 25 => [(5,0)]
  | 26 => [(4,5)]
  | 27 => [(7,0)]
  | 28 => [(0,1),(0,2),(6,4),(6,5)]
  | 29 => [(0,4),(1,1),(1,2),(6,2)]
  | 30 => [(5,4),(8,4)]
  | 31 => [(0,0)]
  | 32 => [(7,2)]
  | 33 => [(0,3),(1,0),(7,0),(8,0)]
  | 34 => [(4,3),(7,1),(8,1),(8,3)]
  | 35 => [(1,5),(3,5),(5,5),(7,5)]
  | _ => [(0,3),(1,0),(6,1)]
def root6Node14Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(5,2)]
  | 5 => some [(8,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(3,0)]
  | 9 => some [(0,4),(6,2)]
  | 10 => some [(5,4),(8,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(0,0)]
  | 15 => some [(1,0),(7,0)]
  | 16 => some [(4,3),(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5)]
  | 21 => some [(6,1)]
  | 22 => some [(4,0),(7,4),(8,0)]
  | 23 => some [(1,3),(6,3),(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(5,0)]
  | 26 => some [(4,5)]
  | 27 => some [(7,0)]
  | 28 => some [(0,1),(0,2),(6,4),(6,5)]
  | 29 => some [(0,4),(1,1),(1,2),(6,2)]
  | 30 => some [(5,4),(8,4)]
  | 31 => some [(0,0)]
  | 32 => some [(7,2)]
  | 33 => some [(0,3),(1,0),(7,0),(8,0)]
  | 34 => some [(4,3),(7,1),(8,1),(8,3)]
  | 35 => some [(1,5),(3,5),(5,5),(7,5)]
  | _ => some [(0,3),(1,0),(6,1)]
theorem root6Node14Domains1_fast_eq : root6Node14Domains1 = expandDomains root6Node14Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node14Domains1 v = expandDomains root6Node14Domains1Fast v from by decide) v
theorem root6Node14Step1Chunk0_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_0⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk0_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_1⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk0_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_2⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk0_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_3⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk0_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_4⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk0_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_5⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk1_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_0⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk1_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_1⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk1_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_2⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk1_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_3⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk1_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_4⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk1_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_5⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk2_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_0⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk2_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_1⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk2_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_2⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk2_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_3⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk2_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_4⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk2_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_5⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk3_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_0⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk3_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_1⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk3_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_2⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk3_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_3⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk3_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_4⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk3_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_5⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk4_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_0⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk4_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_1⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk4_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_2⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk4_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_3⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk4_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_4⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk4_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_5⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk5_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_0⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk5_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_1⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk5_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_2⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk5_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_3⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk5_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_4⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk5_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_5⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk6_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_0⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk6_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_1⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk6_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_2⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk6_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_3⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk6_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_4⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk6_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_5⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk7_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_0⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk7_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_1⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk7_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_2⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk7_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_3⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk7_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_4⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk7_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_5⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk8_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_0⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk8_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_1⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk8_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_2⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk8_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_3⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk8_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_4⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1Chunk8_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_5⟩
      root6Node14Domains0 root6Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains0 root6Node14Domains1
    root6Node14Domains0Fast root6Node14Domains1Fast
    root6Node14Domains0_fast_eq root6Node14Domains1_fast_eq (by decide)
theorem root6Node14Step1_checked :
    checkReplacement table19 root6Node14Domains0 root6Node14Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node14Step1Chunk0_0_checked, root6Node14Step1Chunk0_1_checked, root6Node14Step1Chunk0_2_checked, root6Node14Step1Chunk0_3_checked, root6Node14Step1Chunk0_4_checked, root6Node14Step1Chunk0_5_checked, root6Node14Step1Chunk1_0_checked, root6Node14Step1Chunk1_1_checked, root6Node14Step1Chunk1_2_checked, root6Node14Step1Chunk1_3_checked, root6Node14Step1Chunk1_4_checked, root6Node14Step1Chunk1_5_checked, root6Node14Step1Chunk2_0_checked, root6Node14Step1Chunk2_1_checked, root6Node14Step1Chunk2_2_checked, root6Node14Step1Chunk2_3_checked, root6Node14Step1Chunk2_4_checked, root6Node14Step1Chunk2_5_checked, root6Node14Step1Chunk3_0_checked, root6Node14Step1Chunk3_1_checked, root6Node14Step1Chunk3_2_checked, root6Node14Step1Chunk3_3_checked, root6Node14Step1Chunk3_4_checked, root6Node14Step1Chunk3_5_checked, root6Node14Step1Chunk4_0_checked, root6Node14Step1Chunk4_1_checked, root6Node14Step1Chunk4_2_checked, root6Node14Step1Chunk4_3_checked, root6Node14Step1Chunk4_4_checked, root6Node14Step1Chunk4_5_checked, root6Node14Step1Chunk5_0_checked, root6Node14Step1Chunk5_1_checked, root6Node14Step1Chunk5_2_checked, root6Node14Step1Chunk5_3_checked, root6Node14Step1Chunk5_4_checked, root6Node14Step1Chunk5_5_checked, root6Node14Step1Chunk6_0_checked, root6Node14Step1Chunk6_1_checked, root6Node14Step1Chunk6_2_checked, root6Node14Step1Chunk6_3_checked, root6Node14Step1Chunk6_4_checked, root6Node14Step1Chunk6_5_checked, root6Node14Step1Chunk7_0_checked, root6Node14Step1Chunk7_1_checked, root6Node14Step1Chunk7_2_checked, root6Node14Step1Chunk7_3_checked, root6Node14Step1Chunk7_4_checked, root6Node14Step1Chunk7_5_checked, root6Node14Step1Chunk8_0_checked, root6Node14Step1Chunk8_1_checked, root6Node14Step1Chunk8_2_checked, root6Node14Step1Chunk8_3_checked, root6Node14Step1Chunk8_4_checked, root6Node14Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node14Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(5,2)]
  | 5 => [(8,0)]
  | 6 => [(8,3)]
  | 7 => [(5,5)]
  | 8 => [(3,0)]
  | 9 => [(0,4),(6,2)]
  | 10 => [(5,4),(8,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0)]
  | 15 => [(1,0),(7,0)]
  | 16 => [(4,3),(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(1,5)]
  | 21 => [(6,1)]
  | 22 => [(4,0),(7,4),(8,0)]
  | 23 => [(1,3),(7,3)]
  | 24 => [(8,2)]
  | 25 => [(5,0)]
  | 26 => [(4,5)]
  | 27 => [(7,0)]
  | 28 => [(0,1),(6,4),(6,5)]
  | 29 => [(0,4),(1,2),(6,2)]
  | 30 => [(5,4),(8,4)]
  | 31 => [(0,0)]
  | 32 => [(7,2)]
  | 33 => [(0,3),(1,0),(7,0)]
  | 34 => [(4,3),(7,1),(8,1)]
  | 35 => [(1,5)]
  | _ => [(6,1)]
def root6Node14Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(5,2)]
  | 5 => some [(8,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(3,0)]
  | 9 => some [(0,4),(6,2)]
  | 10 => some [(5,4),(8,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(0,0)]
  | 15 => some [(1,0),(7,0)]
  | 16 => some [(4,3),(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(1,5)]
  | 21 => some [(6,1)]
  | 22 => some [(4,0),(7,4),(8,0)]
  | 23 => some [(1,3),(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(5,0)]
  | 26 => some [(4,5)]
  | 27 => some [(7,0)]
  | 28 => some [(0,1),(6,4),(6,5)]
  | 29 => some [(0,4),(1,2),(6,2)]
  | 30 => some [(5,4),(8,4)]
  | 31 => some [(0,0)]
  | 32 => some [(7,2)]
  | 33 => some [(0,3),(1,0),(7,0)]
  | 34 => some [(4,3),(7,1),(8,1)]
  | 35 => some [(1,5)]
  | _ => some [(6,1)]
theorem root6Node14Domains2_fast_eq : root6Node14Domains2 = expandDomains root6Node14Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node14Domains2 v = expandDomains root6Node14Domains2Fast v from by decide) v
theorem root6Node14Step2Chunk0_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_0⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk0_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_1⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk0_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_2⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk0_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_3⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk0_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_4⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk0_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_5⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk1_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_0⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk1_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_1⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk1_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_2⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk1_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_3⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk1_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_4⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk1_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_5⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk2_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_0⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk2_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_1⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk2_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_2⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk2_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_3⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk2_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_4⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk2_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_5⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk3_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_0⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk3_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_1⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk3_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_2⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk3_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_3⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk3_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_4⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk3_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_5⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk4_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_0⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk4_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_1⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk4_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_2⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk4_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_3⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk4_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_4⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk4_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_5⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk5_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_0⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk5_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_1⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk5_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_2⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk5_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_3⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk5_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_4⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk5_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_5⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk6_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_0⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk6_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_1⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk6_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_2⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk6_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_3⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk6_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_4⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk6_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_5⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk7_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_0⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk7_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_1⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk7_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_2⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk7_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_3⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk7_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_4⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk7_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_5⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk8_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_0⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk8_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_1⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk8_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_2⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk8_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_3⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk8_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_4⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2Chunk8_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_5⟩
      root6Node14Domains1 root6Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node14Domains1 root6Node14Domains2
    root6Node14Domains1Fast root6Node14Domains2Fast
    root6Node14Domains1_fast_eq root6Node14Domains2_fast_eq (by decide)
theorem root6Node14Step2_checked :
    checkReplacement table30 root6Node14Domains1 root6Node14Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node14Step2Chunk0_0_checked, root6Node14Step2Chunk0_1_checked, root6Node14Step2Chunk0_2_checked, root6Node14Step2Chunk0_3_checked, root6Node14Step2Chunk0_4_checked, root6Node14Step2Chunk0_5_checked, root6Node14Step2Chunk1_0_checked, root6Node14Step2Chunk1_1_checked, root6Node14Step2Chunk1_2_checked, root6Node14Step2Chunk1_3_checked, root6Node14Step2Chunk1_4_checked, root6Node14Step2Chunk1_5_checked, root6Node14Step2Chunk2_0_checked, root6Node14Step2Chunk2_1_checked, root6Node14Step2Chunk2_2_checked, root6Node14Step2Chunk2_3_checked, root6Node14Step2Chunk2_4_checked, root6Node14Step2Chunk2_5_checked, root6Node14Step2Chunk3_0_checked, root6Node14Step2Chunk3_1_checked, root6Node14Step2Chunk3_2_checked, root6Node14Step2Chunk3_3_checked, root6Node14Step2Chunk3_4_checked, root6Node14Step2Chunk3_5_checked, root6Node14Step2Chunk4_0_checked, root6Node14Step2Chunk4_1_checked, root6Node14Step2Chunk4_2_checked, root6Node14Step2Chunk4_3_checked, root6Node14Step2Chunk4_4_checked, root6Node14Step2Chunk4_5_checked, root6Node14Step2Chunk5_0_checked, root6Node14Step2Chunk5_1_checked, root6Node14Step2Chunk5_2_checked, root6Node14Step2Chunk5_3_checked, root6Node14Step2Chunk5_4_checked, root6Node14Step2Chunk5_5_checked, root6Node14Step2Chunk6_0_checked, root6Node14Step2Chunk6_1_checked, root6Node14Step2Chunk6_2_checked, root6Node14Step2Chunk6_3_checked, root6Node14Step2Chunk6_4_checked, root6Node14Step2Chunk6_5_checked, root6Node14Step2Chunk7_0_checked, root6Node14Step2Chunk7_1_checked, root6Node14Step2Chunk7_2_checked, root6Node14Step2Chunk7_3_checked, root6Node14Step2Chunk7_4_checked, root6Node14Step2Chunk7_5_checked, root6Node14Step2Chunk8_0_checked, root6Node14Step2Chunk8_1_checked, root6Node14Step2Chunk8_2_checked, root6Node14Step2Chunk8_3_checked, root6Node14Step2Chunk8_4_checked, root6Node14Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
