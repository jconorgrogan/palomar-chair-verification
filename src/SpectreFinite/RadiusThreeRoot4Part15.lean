module

public import SpectreFinite.RadiusThreeRoot4Part14
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable19
public import SpectreFinite.RadiusThreeTable26
public import SpectreFinite.RadiusThreeTable30

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node24Domains0 : Domains 37 State := restrict root4Node23Domains3 8 (1,4)
def root4Node24Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(2,2)]
  | 1 => some [(3,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(1,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(8,4)]
  | 8 => some [(1,4)]
  | 9 => some [(5,0)]
  | 10 => some [(4,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3),(6,0)]
  | 15 => some [(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(7,2)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2),(8,2)]
  | 21 => some [(5,0),(5,3),(8,0)]
  | 22 => some [(1,5)]
  | 23 => some [(6,1)]
  | 24 => some [(5,1)]
  | 25 => some [(0,1)]
  | 26 => some [(6,2)]
  | 27 => some [(7,4),(8,4)]
  | 28 => some [(7,0)]
  | 29 => some [(8,3)]
  | 30 => some [(5,5),(8,5)]
  | 31 => some [(1,0)]
  | 32 => some [(2,1),(7,1)]
  | 33 => some [(1,4),(7,4)]
  | 34 => some [(0,5),(1,3),(6,3)]
  | 35 => some [(4,4),(7,2),(8,2)]
  | _ => some [(0,0),(4,0),(5,0),(8,0)]
theorem root4Node24Domains0_fast_eq : root4Node24Domains0 = expandDomains root4Node24Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node24Domains0 v = expandDomains root4Node24Domains0Fast v from by decide) v
def root4Node24Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(2,2)]
  | 1 => [(3,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(1,1)]
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
  | 21 => [(5,0),(8,0)]
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
  | 33 => [(1,4),(7,4)]
  | 34 => [(0,5),(1,3),(6,3)]
  | 35 => [(4,4),(7,2),(8,2)]
  | _ => [(0,0),(4,0),(5,0),(8,0)]
def root4Node24Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(2,2)]
  | 1 => some [(3,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(1,1)]
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
  | 21 => some [(5,0),(8,0)]
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
  | 33 => some [(1,4),(7,4)]
  | 34 => some [(0,5),(1,3),(6,3)]
  | 35 => some [(4,4),(7,2),(8,2)]
  | _ => some [(0,0),(4,0),(5,0),(8,0)]
theorem root4Node24Domains1_fast_eq : root4Node24Domains1 = expandDomains root4Node24Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node24Domains1 v = expandDomains root4Node24Domains1Fast v from by decide) v
theorem root4Node24Step1Chunk0_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_0⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk0_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_1⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk0_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_2⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk0_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_3⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk0_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_4⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk0_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_5⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk1_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_0⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk1_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_1⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk1_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_2⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk1_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_3⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk1_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_4⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk1_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_5⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk2_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_0⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk2_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_1⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk2_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_2⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk2_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_3⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk2_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_4⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk2_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_5⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk3_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_0⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk3_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_1⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk3_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_2⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk3_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_3⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk3_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_4⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk3_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_5⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk4_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_0⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk4_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_1⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk4_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_2⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk4_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_3⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk4_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_4⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk4_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_5⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk5_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_0⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk5_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_1⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk5_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_2⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk5_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_3⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk5_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_4⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk5_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_5⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk6_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_0⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk6_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_1⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk6_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_2⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk6_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_3⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk6_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_4⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk6_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_5⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk7_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_0⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk7_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_1⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk7_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_2⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk7_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_3⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk7_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_4⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk7_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_5⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk8_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_0⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk8_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_1⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk8_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_2⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk8_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_3⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk8_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_4⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1Chunk8_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_5⟩
      root4Node24Domains0 root4Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains0 root4Node24Domains1
    root4Node24Domains0Fast root4Node24Domains1Fast
    root4Node24Domains0_fast_eq root4Node24Domains1_fast_eq (by decide)
theorem root4Node24Step1_checked :
    checkReplacement table19 root4Node24Domains0 root4Node24Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node24Step1Chunk0_0_checked, root4Node24Step1Chunk0_1_checked, root4Node24Step1Chunk0_2_checked, root4Node24Step1Chunk0_3_checked, root4Node24Step1Chunk0_4_checked, root4Node24Step1Chunk0_5_checked, root4Node24Step1Chunk1_0_checked, root4Node24Step1Chunk1_1_checked, root4Node24Step1Chunk1_2_checked, root4Node24Step1Chunk1_3_checked, root4Node24Step1Chunk1_4_checked, root4Node24Step1Chunk1_5_checked, root4Node24Step1Chunk2_0_checked, root4Node24Step1Chunk2_1_checked, root4Node24Step1Chunk2_2_checked, root4Node24Step1Chunk2_3_checked, root4Node24Step1Chunk2_4_checked, root4Node24Step1Chunk2_5_checked, root4Node24Step1Chunk3_0_checked, root4Node24Step1Chunk3_1_checked, root4Node24Step1Chunk3_2_checked, root4Node24Step1Chunk3_3_checked, root4Node24Step1Chunk3_4_checked, root4Node24Step1Chunk3_5_checked, root4Node24Step1Chunk4_0_checked, root4Node24Step1Chunk4_1_checked, root4Node24Step1Chunk4_2_checked, root4Node24Step1Chunk4_3_checked, root4Node24Step1Chunk4_4_checked, root4Node24Step1Chunk4_5_checked, root4Node24Step1Chunk5_0_checked, root4Node24Step1Chunk5_1_checked, root4Node24Step1Chunk5_2_checked, root4Node24Step1Chunk5_3_checked, root4Node24Step1Chunk5_4_checked, root4Node24Step1Chunk5_5_checked, root4Node24Step1Chunk6_0_checked, root4Node24Step1Chunk6_1_checked, root4Node24Step1Chunk6_2_checked, root4Node24Step1Chunk6_3_checked, root4Node24Step1Chunk6_4_checked, root4Node24Step1Chunk6_5_checked, root4Node24Step1Chunk7_0_checked, root4Node24Step1Chunk7_1_checked, root4Node24Step1Chunk7_2_checked, root4Node24Step1Chunk7_3_checked, root4Node24Step1Chunk7_4_checked, root4Node24Step1Chunk7_5_checked, root4Node24Step1Chunk8_0_checked, root4Node24Step1Chunk8_1_checked, root4Node24Step1Chunk8_2_checked, root4Node24Step1Chunk8_3_checked, root4Node24Step1Chunk8_4_checked, root4Node24Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node24Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(2,2)]
  | 1 => [(3,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(1,1)]
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
  | 21 => [(5,0),(8,0)]
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
  | _ => [(4,0),(5,0),(8,0)]
def root4Node24Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(2,2)]
  | 1 => some [(3,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(1,1)]
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
  | 21 => some [(5,0),(8,0)]
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
theorem root4Node24Domains2_fast_eq : root4Node24Domains2 = expandDomains root4Node24Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node24Domains2 v = expandDomains root4Node24Domains2Fast v from by decide) v
theorem root4Node24Step2Chunk0_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_0⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk0_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_1⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk0_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_2⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk0_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_3⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk0_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_4⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk0_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_5⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk1_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_0⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk1_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_1⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk1_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_2⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk1_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_3⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk1_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_4⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk1_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_5⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk2_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_0⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk2_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_1⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk2_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_2⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk2_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_3⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk2_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_4⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk2_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_5⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk3_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_0⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk3_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_1⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk3_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_2⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk3_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_3⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk3_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_4⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk3_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_5⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk4_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_0⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk4_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_1⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk4_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_2⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk4_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_3⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk4_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_4⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk4_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_5⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk5_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_0⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk5_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_1⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk5_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_2⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk5_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_3⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk5_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_4⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk5_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_5⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk6_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_0⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk6_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_1⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk6_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_2⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk6_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_3⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk6_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_4⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk6_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_5⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk7_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_0⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk7_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_1⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk7_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_2⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk7_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_3⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk7_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_4⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk7_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_5⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk8_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_0⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk8_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_1⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk8_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_2⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk8_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_3⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk8_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_4⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2Chunk8_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_5⟩
      root4Node24Domains1 root4Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node24Domains1 root4Node24Domains2
    root4Node24Domains1Fast root4Node24Domains2Fast
    root4Node24Domains1_fast_eq root4Node24Domains2_fast_eq (by decide)
theorem root4Node24Step2_checked :
    checkReplacement table30 root4Node24Domains1 root4Node24Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node24Step2Chunk0_0_checked, root4Node24Step2Chunk0_1_checked, root4Node24Step2Chunk0_2_checked, root4Node24Step2Chunk0_3_checked, root4Node24Step2Chunk0_4_checked, root4Node24Step2Chunk0_5_checked, root4Node24Step2Chunk1_0_checked, root4Node24Step2Chunk1_1_checked, root4Node24Step2Chunk1_2_checked, root4Node24Step2Chunk1_3_checked, root4Node24Step2Chunk1_4_checked, root4Node24Step2Chunk1_5_checked, root4Node24Step2Chunk2_0_checked, root4Node24Step2Chunk2_1_checked, root4Node24Step2Chunk2_2_checked, root4Node24Step2Chunk2_3_checked, root4Node24Step2Chunk2_4_checked, root4Node24Step2Chunk2_5_checked, root4Node24Step2Chunk3_0_checked, root4Node24Step2Chunk3_1_checked, root4Node24Step2Chunk3_2_checked, root4Node24Step2Chunk3_3_checked, root4Node24Step2Chunk3_4_checked, root4Node24Step2Chunk3_5_checked, root4Node24Step2Chunk4_0_checked, root4Node24Step2Chunk4_1_checked, root4Node24Step2Chunk4_2_checked, root4Node24Step2Chunk4_3_checked, root4Node24Step2Chunk4_4_checked, root4Node24Step2Chunk4_5_checked, root4Node24Step2Chunk5_0_checked, root4Node24Step2Chunk5_1_checked, root4Node24Step2Chunk5_2_checked, root4Node24Step2Chunk5_3_checked, root4Node24Step2Chunk5_4_checked, root4Node24Step2Chunk5_5_checked, root4Node24Step2Chunk6_0_checked, root4Node24Step2Chunk6_1_checked, root4Node24Step2Chunk6_2_checked, root4Node24Step2Chunk6_3_checked, root4Node24Step2Chunk6_4_checked, root4Node24Step2Chunk6_5_checked, root4Node24Step2Chunk7_0_checked, root4Node24Step2Chunk7_1_checked, root4Node24Step2Chunk7_2_checked, root4Node24Step2Chunk7_3_checked, root4Node24Step2Chunk7_4_checked, root4Node24Step2Chunk7_5_checked, root4Node24Step2Chunk8_0_checked, root4Node24Step2Chunk8_1_checked, root4Node24Step2Chunk8_2_checked, root4Node24Step2Chunk8_3_checked, root4Node24Step2Chunk8_4_checked, root4Node24Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node25Domains0 : Domains 37 State := restrict root4Node24Domains2 21 (5,0)
def root4Node25Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(2,2)]
  | 1 => some [(3,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(1,1)]
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
theorem root4Node25Domains0_fast_eq : root4Node25Domains0 = expandDomains root4Node25Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node25Domains0 v = expandDomains root4Node25Domains0Fast v from by decide) v
def root4Node25Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(2,2)]
  | 1 => [(3,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(1,1)]
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
def root4Node25Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(2,2)]
  | 1 => some [(3,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(1,1)]
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
theorem root4Node25Domains1_fast_eq : root4Node25Domains1 = expandDomains root4Node25Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root4Node25Domains1 v = expandDomains root4Node25Domains1Fast v from by decide) v
theorem root4Node25Step1Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root4Node25Domains0 root4Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node25Domains0 root4Node25Domains1
    root4Node25Domains0Fast root4Node25Domains1Fast
    root4Node25Domains0_fast_eq root4Node25Domains1_fast_eq (by decide)
theorem root4Node25Step1_checked :
    checkReplacement table26 root4Node25Domains0 root4Node25Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node25Step1Chunk0_0_checked, root4Node25Step1Chunk0_1_checked, root4Node25Step1Chunk0_2_checked, root4Node25Step1Chunk0_3_checked, root4Node25Step1Chunk0_4_checked, root4Node25Step1Chunk0_5_checked, root4Node25Step1Chunk1_0_checked, root4Node25Step1Chunk1_1_checked, root4Node25Step1Chunk1_2_checked, root4Node25Step1Chunk1_3_checked, root4Node25Step1Chunk1_4_checked, root4Node25Step1Chunk1_5_checked, root4Node25Step1Chunk2_0_checked, root4Node25Step1Chunk2_1_checked, root4Node25Step1Chunk2_2_checked, root4Node25Step1Chunk2_3_checked, root4Node25Step1Chunk2_4_checked, root4Node25Step1Chunk2_5_checked, root4Node25Step1Chunk3_0_checked, root4Node25Step1Chunk3_1_checked, root4Node25Step1Chunk3_2_checked, root4Node25Step1Chunk3_3_checked, root4Node25Step1Chunk3_4_checked, root4Node25Step1Chunk3_5_checked, root4Node25Step1Chunk4_0_checked, root4Node25Step1Chunk4_1_checked, root4Node25Step1Chunk4_2_checked, root4Node25Step1Chunk4_3_checked, root4Node25Step1Chunk4_4_checked, root4Node25Step1Chunk4_5_checked, root4Node25Step1Chunk5_0_checked, root4Node25Step1Chunk5_1_checked, root4Node25Step1Chunk5_2_checked, root4Node25Step1Chunk5_3_checked, root4Node25Step1Chunk5_4_checked, root4Node25Step1Chunk5_5_checked, root4Node25Step1Chunk6_0_checked, root4Node25Step1Chunk6_1_checked, root4Node25Step1Chunk6_2_checked, root4Node25Step1Chunk6_3_checked, root4Node25Step1Chunk6_4_checked, root4Node25Step1Chunk6_5_checked, root4Node25Step1Chunk7_0_checked, root4Node25Step1Chunk7_1_checked, root4Node25Step1Chunk7_2_checked, root4Node25Step1Chunk7_3_checked, root4Node25Step1Chunk7_4_checked, root4Node25Step1Chunk7_5_checked, root4Node25Step1Chunk8_0_checked, root4Node25Step1Chunk8_1_checked, root4Node25Step1Chunk8_2_checked, root4Node25Step1Chunk8_3_checked, root4Node25Step1Chunk8_4_checked, root4Node25Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
