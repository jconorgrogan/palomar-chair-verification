module

public import SpectreFinite.RadiusThreeRoot6Part13
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable13
public import SpectreFinite.RadiusThreeTable23
public import SpectreFinite.RadiusThreeTable25

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node27Domains0 : Domains 37 State := restrict root6Node19Domains3 9 (6,2)
def root6Node27Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(5,2)]
  | 5 => some [(8,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(7,0)]
  | 9 => some [(6,2)]
  | 10 => some [(5,4),(8,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(1,4),(6,4)]
  | 15 => some [(1,0),(7,0)]
  | 16 => some [(4,3),(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(4,0),(7,4)]
  | 23 => some [(1,3),(6,3),(7,3)]
  | 24 => some [(7,2),(8,2)]
  | 25 => some [(4,0),(8,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2),(8,2)]
  | 28 => some [(0,1),(0,2),(6,5)]
  | 29 => some [(0,4),(1,1),(6,2)]
  | 30 => some [(5,1),(5,4),(8,4)]
  | 31 => some [(0,1),(6,4)]
  | 32 => some [(1,2),(6,2)]
  | 33 => some [(1,0),(7,0),(8,0)]
  | 34 => some [(4,3),(7,1),(8,3)]
  | 35 => some [(3,5),(5,5),(7,5)]
  | _ => some [(0,3),(1,0)]
theorem root6Node27Domains0_fast_eq : root6Node27Domains0 = expandDomains root6Node27Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node27Domains0 v = expandDomains root6Node27Domains0Fast v from by decide) v
def root6Node27Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(5,2)]
  | 5 => [(8,0)]
  | 6 => [(8,3)]
  | 7 => [(5,5)]
  | 8 => [(7,0)]
  | 9 => [(6,2)]
  | 10 => [(8,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(1,4),(6,4)]
  | 15 => [(1,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(0,3),(6,0)]
  | 22 => [(4,0)]
  | 23 => [(7,3)]
  | 24 => [(8,2)]
  | 25 => [(8,0)]
  | 26 => [(7,3)]
  | 27 => [(4,2),(8,2)]
  | 28 => [(0,1)]
  | 29 => [(6,2)]
  | 30 => [(8,4)]
  | 31 => [(0,1),(6,4)]
  | 32 => [(1,2),(6,2)]
  | 33 => [(1,0)]
  | 34 => [(7,1)]
  | 35 => [(3,5),(5,5),(7,5)]
  | _ => [(0,3),(1,0)]
def root6Node27Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(5,2)]
  | 5 => some [(8,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(7,0)]
  | 9 => some [(6,2)]
  | 10 => some [(8,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(1,4),(6,4)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(4,0)]
  | 23 => some [(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(8,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2),(8,2)]
  | 28 => some [(0,1)]
  | 29 => some [(6,2)]
  | 30 => some [(8,4)]
  | 31 => some [(0,1),(6,4)]
  | 32 => some [(1,2),(6,2)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(3,5),(5,5),(7,5)]
  | _ => some [(0,3),(1,0)]
theorem root6Node27Domains1_fast_eq : root6Node27Domains1 = expandDomains root6Node27Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node27Domains1 v = expandDomains root6Node27Domains1Fast v from by decide) v
theorem root6Node27Step1Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root6Node27Domains0 root6Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains0 root6Node27Domains1
    root6Node27Domains0Fast root6Node27Domains1Fast
    root6Node27Domains0_fast_eq root6Node27Domains1_fast_eq (by decide)
theorem root6Node27Step1_checked :
    checkReplacement table23 root6Node27Domains0 root6Node27Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node27Step1Chunk0_0_checked, root6Node27Step1Chunk0_1_checked, root6Node27Step1Chunk0_2_checked, root6Node27Step1Chunk0_3_checked, root6Node27Step1Chunk0_4_checked, root6Node27Step1Chunk0_5_checked, root6Node27Step1Chunk1_0_checked, root6Node27Step1Chunk1_1_checked, root6Node27Step1Chunk1_2_checked, root6Node27Step1Chunk1_3_checked, root6Node27Step1Chunk1_4_checked, root6Node27Step1Chunk1_5_checked, root6Node27Step1Chunk2_0_checked, root6Node27Step1Chunk2_1_checked, root6Node27Step1Chunk2_2_checked, root6Node27Step1Chunk2_3_checked, root6Node27Step1Chunk2_4_checked, root6Node27Step1Chunk2_5_checked, root6Node27Step1Chunk3_0_checked, root6Node27Step1Chunk3_1_checked, root6Node27Step1Chunk3_2_checked, root6Node27Step1Chunk3_3_checked, root6Node27Step1Chunk3_4_checked, root6Node27Step1Chunk3_5_checked, root6Node27Step1Chunk4_0_checked, root6Node27Step1Chunk4_1_checked, root6Node27Step1Chunk4_2_checked, root6Node27Step1Chunk4_3_checked, root6Node27Step1Chunk4_4_checked, root6Node27Step1Chunk4_5_checked, root6Node27Step1Chunk5_0_checked, root6Node27Step1Chunk5_1_checked, root6Node27Step1Chunk5_2_checked, root6Node27Step1Chunk5_3_checked, root6Node27Step1Chunk5_4_checked, root6Node27Step1Chunk5_5_checked, root6Node27Step1Chunk6_0_checked, root6Node27Step1Chunk6_1_checked, root6Node27Step1Chunk6_2_checked, root6Node27Step1Chunk6_3_checked, root6Node27Step1Chunk6_4_checked, root6Node27Step1Chunk6_5_checked, root6Node27Step1Chunk7_0_checked, root6Node27Step1Chunk7_1_checked, root6Node27Step1Chunk7_2_checked, root6Node27Step1Chunk7_3_checked, root6Node27Step1Chunk7_4_checked, root6Node27Step1Chunk7_5_checked, root6Node27Step1Chunk8_0_checked, root6Node27Step1Chunk8_1_checked, root6Node27Step1Chunk8_2_checked, root6Node27Step1Chunk8_3_checked, root6Node27Step1Chunk8_4_checked, root6Node27Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node27Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(5,2)]
  | 5 => [(8,0)]
  | 6 => [(8,3)]
  | 7 => [(5,5)]
  | 8 => [(7,0)]
  | 9 => [(6,2)]
  | 10 => [(8,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(1,4),(6,4)]
  | 15 => [(1,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(0,3),(6,0)]
  | 22 => [(4,0)]
  | 23 => [(7,3)]
  | 24 => [(8,2)]
  | 25 => [(8,0)]
  | 26 => [(7,3)]
  | 27 => [(4,2),(8,2)]
  | 28 => [(0,1)]
  | 29 => [(6,2)]
  | 30 => [(8,4)]
  | 31 => [(6,4)]
  | 32 => [(1,2)]
  | 33 => [(1,0)]
  | 34 => [(7,1)]
  | 35 => [(7,5)]
  | _ => [(0,3)]
def root6Node27Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(5,2)]
  | 5 => some [(8,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(7,0)]
  | 9 => some [(6,2)]
  | 10 => some [(8,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(1,4),(6,4)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(4,0)]
  | 23 => some [(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(8,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2),(8,2)]
  | 28 => some [(0,1)]
  | 29 => some [(6,2)]
  | 30 => some [(8,4)]
  | 31 => some [(6,4)]
  | 32 => some [(1,2)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(7,5)]
  | _ => some [(0,3)]
theorem root6Node27Domains2_fast_eq : root6Node27Domains2 = expandDomains root6Node27Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node27Domains2 v = expandDomains root6Node27Domains2Fast v from by decide) v
theorem root6Node27Step2Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root6Node27Domains1 root6Node27Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node27Domains1 root6Node27Domains2
    root6Node27Domains1Fast root6Node27Domains2Fast
    root6Node27Domains1_fast_eq root6Node27Domains2_fast_eq (by decide)
theorem root6Node27Step2_checked :
    checkReplacement table25 root6Node27Domains1 root6Node27Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node27Step2Chunk0_0_checked, root6Node27Step2Chunk0_1_checked, root6Node27Step2Chunk0_2_checked, root6Node27Step2Chunk0_3_checked, root6Node27Step2Chunk0_4_checked, root6Node27Step2Chunk0_5_checked, root6Node27Step2Chunk1_0_checked, root6Node27Step2Chunk1_1_checked, root6Node27Step2Chunk1_2_checked, root6Node27Step2Chunk1_3_checked, root6Node27Step2Chunk1_4_checked, root6Node27Step2Chunk1_5_checked, root6Node27Step2Chunk2_0_checked, root6Node27Step2Chunk2_1_checked, root6Node27Step2Chunk2_2_checked, root6Node27Step2Chunk2_3_checked, root6Node27Step2Chunk2_4_checked, root6Node27Step2Chunk2_5_checked, root6Node27Step2Chunk3_0_checked, root6Node27Step2Chunk3_1_checked, root6Node27Step2Chunk3_2_checked, root6Node27Step2Chunk3_3_checked, root6Node27Step2Chunk3_4_checked, root6Node27Step2Chunk3_5_checked, root6Node27Step2Chunk4_0_checked, root6Node27Step2Chunk4_1_checked, root6Node27Step2Chunk4_2_checked, root6Node27Step2Chunk4_3_checked, root6Node27Step2Chunk4_4_checked, root6Node27Step2Chunk4_5_checked, root6Node27Step2Chunk5_0_checked, root6Node27Step2Chunk5_1_checked, root6Node27Step2Chunk5_2_checked, root6Node27Step2Chunk5_3_checked, root6Node27Step2Chunk5_4_checked, root6Node27Step2Chunk5_5_checked, root6Node27Step2Chunk6_0_checked, root6Node27Step2Chunk6_1_checked, root6Node27Step2Chunk6_2_checked, root6Node27Step2Chunk6_3_checked, root6Node27Step2Chunk6_4_checked, root6Node27Step2Chunk6_5_checked, root6Node27Step2Chunk7_0_checked, root6Node27Step2Chunk7_1_checked, root6Node27Step2Chunk7_2_checked, root6Node27Step2Chunk7_3_checked, root6Node27Step2Chunk7_4_checked, root6Node27Step2Chunk7_5_checked, root6Node27Step2Chunk8_0_checked, root6Node27Step2Chunk8_1_checked, root6Node27Step2Chunk8_2_checked, root6Node27Step2Chunk8_3_checked, root6Node27Step2Chunk8_4_checked, root6Node27Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node28Domains0 : Domains 37 State := restrict root6Node27Domains2 14 (1,4)
def root6Node28Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(5,2)]
  | 5 => some [(8,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(7,0)]
  | 9 => some [(6,2)]
  | 10 => some [(8,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(1,4)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3),(6,0)]
  | 22 => some [(4,0)]
  | 23 => some [(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(8,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2),(8,2)]
  | 28 => some [(0,1)]
  | 29 => some [(6,2)]
  | 30 => some [(8,4)]
  | 31 => some [(6,4)]
  | 32 => some [(1,2)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(7,5)]
  | _ => some [(0,3)]
theorem root6Node28Domains0_fast_eq : root6Node28Domains0 = expandDomains root6Node28Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node28Domains0 v = expandDomains root6Node28Domains0Fast v from by decide) v
def root6Node28Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(5,2)]
  | 5 => [(8,0)]
  | 6 => [(8,3)]
  | 7 => [(5,5)]
  | 8 => [(7,0)]
  | 9 => [(6,2)]
  | 10 => [(8,4)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(1,4)]
  | 15 => [(1,0)]
  | 16 => [(7,1)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(4,0)]
  | 23 => [(7,3)]
  | 24 => [(8,2)]
  | 25 => [(8,0)]
  | 26 => [(7,3)]
  | 27 => [(8,2)]
  | 28 => [(0,1)]
  | 29 => [(6,2)]
  | 30 => [(8,4)]
  | 31 => [(6,4)]
  | 32 => [(1,2)]
  | 33 => [(1,0)]
  | 34 => [(7,1)]
  | 35 => [(7,5)]
  | _ => [(0,3)]
def root6Node28Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(5,2)]
  | 5 => some [(8,0)]
  | 6 => some [(8,3)]
  | 7 => some [(5,5)]
  | 8 => some [(7,0)]
  | 9 => some [(6,2)]
  | 10 => some [(8,4)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(1,4)]
  | 15 => some [(1,0)]
  | 16 => some [(7,1)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(4,0)]
  | 23 => some [(7,3)]
  | 24 => some [(8,2)]
  | 25 => some [(8,0)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(0,1)]
  | 29 => some [(6,2)]
  | 30 => some [(8,4)]
  | 31 => some [(6,4)]
  | 32 => some [(1,2)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(7,5)]
  | _ => some [(0,3)]
theorem root6Node28Domains1_fast_eq : root6Node28Domains1 = expandDomains root6Node28Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root6Node28Domains1 v = expandDomains root6Node28Domains1Fast v from by decide) v
theorem root6Node28Step1Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root6Node28Domains0 root6Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node28Domains0 root6Node28Domains1
    root6Node28Domains0Fast root6Node28Domains1Fast
    root6Node28Domains0_fast_eq root6Node28Domains1_fast_eq (by decide)
theorem root6Node28Step1_checked :
    checkReplacement table13 root6Node28Domains0 root6Node28Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node28Step1Chunk0_0_checked, root6Node28Step1Chunk0_1_checked, root6Node28Step1Chunk0_2_checked, root6Node28Step1Chunk0_3_checked, root6Node28Step1Chunk0_4_checked, root6Node28Step1Chunk0_5_checked, root6Node28Step1Chunk1_0_checked, root6Node28Step1Chunk1_1_checked, root6Node28Step1Chunk1_2_checked, root6Node28Step1Chunk1_3_checked, root6Node28Step1Chunk1_4_checked, root6Node28Step1Chunk1_5_checked, root6Node28Step1Chunk2_0_checked, root6Node28Step1Chunk2_1_checked, root6Node28Step1Chunk2_2_checked, root6Node28Step1Chunk2_3_checked, root6Node28Step1Chunk2_4_checked, root6Node28Step1Chunk2_5_checked, root6Node28Step1Chunk3_0_checked, root6Node28Step1Chunk3_1_checked, root6Node28Step1Chunk3_2_checked, root6Node28Step1Chunk3_3_checked, root6Node28Step1Chunk3_4_checked, root6Node28Step1Chunk3_5_checked, root6Node28Step1Chunk4_0_checked, root6Node28Step1Chunk4_1_checked, root6Node28Step1Chunk4_2_checked, root6Node28Step1Chunk4_3_checked, root6Node28Step1Chunk4_4_checked, root6Node28Step1Chunk4_5_checked, root6Node28Step1Chunk5_0_checked, root6Node28Step1Chunk5_1_checked, root6Node28Step1Chunk5_2_checked, root6Node28Step1Chunk5_3_checked, root6Node28Step1Chunk5_4_checked, root6Node28Step1Chunk5_5_checked, root6Node28Step1Chunk6_0_checked, root6Node28Step1Chunk6_1_checked, root6Node28Step1Chunk6_2_checked, root6Node28Step1Chunk6_3_checked, root6Node28Step1Chunk6_4_checked, root6Node28Step1Chunk6_5_checked, root6Node28Step1Chunk7_0_checked, root6Node28Step1Chunk7_1_checked, root6Node28Step1Chunk7_2_checked, root6Node28Step1Chunk7_3_checked, root6Node28Step1Chunk7_4_checked, root6Node28Step1Chunk7_5_checked, root6Node28Step1Chunk8_0_checked, root6Node28Step1Chunk8_1_checked, root6Node28Step1Chunk8_2_checked, root6Node28Step1Chunk8_3_checked, root6Node28Step1Chunk8_4_checked, root6Node28Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root6Node28Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node28Domains1 (.output 13) = true := by decide
end SpectreFinite.HexSearch.RadiusThree
