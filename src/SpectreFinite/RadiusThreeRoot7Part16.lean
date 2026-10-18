module

public import SpectreFinite.RadiusThreeRoot7Part15
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable13
public import SpectreFinite.RadiusThreeTable16
public import SpectreFinite.RadiusThreeTable25

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node24Domains0 : Domains 37 State := restrict root7Node23Domains0 3 (1,0)
def root7Node24Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(1,0)]
  | 4 => some [(1,2),(6,2)]
  | 5 => some [(8,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(4,0),(7,4)]
  | 9 => some [(0,3),(1,0)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(4,1),(5,1),(8,1)]
  | 14 => some [(0,1),(0,2),(6,5)]
  | 15 => some [(4,2),(8,2)]
  | 16 => some [(5,0),(5,3)]
  | 17 => some [(4,5),(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5),(8,5)]
  | 21 => some [(1,0),(3,0),(5,0),(7,0)]
  | 22 => some [(1,4),(3,4),(5,4),(7,4)]
  | 23 => some [(0,0),(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(6,4),(7,4)]
  | 26 => some [(0,5),(1,2),(1,3),(6,3)]
  | 27 => some [(4,4),(7,2),(8,2),(8,4)]
  | 28 => some [(0,2),(1,5),(6,0)]
  | 29 => some [(1,1),(6,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(0,3),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(7,1),(8,1)]
  | 33 => some [(2,0),(4,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(4,2),(5,2),(5,5),(8,2)]
  | _ => some [(5,0),(5,3),(7,0),(8,0)]
theorem root7Node24Domains0_fast_eq : root7Node24Domains0 = expandDomains root7Node24Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node24Domains0 v = expandDomains root7Node24Domains0Fast v from by decide) v
def root7Node24Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0)]
  | 2 => [(4,5)]
  | 3 => [(1,0)]
  | 4 => [(1,2),(6,2)]
  | 5 => [(8,4)]
  | 6 => [(0,0)]
  | 7 => [(7,2)]
  | 8 => [(4,0)]
  | 9 => [(0,3),(1,0)]
  | 10 => [(7,1),(8,1)]
  | 11 => [(1,5)]
  | 12 => [(6,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(4,2),(8,2)]
  | 16 => [(5,0),(5,3)]
  | 17 => [(4,5),(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5),(8,5)]
  | 21 => [(1,0)]
  | 22 => [(1,4),(3,4),(5,4),(7,4)]
  | 23 => [(0,0),(0,5),(6,3)]
  | 24 => [(4,4),(7,2)]
  | 25 => [(1,4),(7,4)]
  | 26 => [(0,5),(1,3),(6,3)]
  | 27 => [(4,4),(7,2),(8,2)]
  | 28 => [(0,2),(1,5),(6,0)]
  | 29 => [(1,1),(6,1),(7,1)]
  | 30 => [(4,1),(7,5),(8,1)]
  | 31 => [(0,2),(0,3),(6,0),(6,5)]
  | 32 => [(0,4),(1,1),(7,1),(8,1)]
  | 33 => [(2,0),(4,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(4,2),(5,2),(5,5),(8,2)]
  | _ => [(5,0),(5,3),(7,0),(8,0)]
def root7Node24Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(1,0)]
  | 4 => some [(1,2),(6,2)]
  | 5 => some [(8,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(4,0)]
  | 9 => some [(0,3),(1,0)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(5,1)]
  | 14 => some [(0,1)]
  | 15 => some [(4,2),(8,2)]
  | 16 => some [(5,0),(5,3)]
  | 17 => some [(4,5),(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5),(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(1,4),(3,4),(5,4),(7,4)]
  | 23 => some [(0,0),(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(7,4)]
  | 26 => some [(0,5),(1,3),(6,3)]
  | 27 => some [(4,4),(7,2),(8,2)]
  | 28 => some [(0,2),(1,5),(6,0)]
  | 29 => some [(1,1),(6,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(0,3),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(7,1),(8,1)]
  | 33 => some [(2,0),(4,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(4,2),(5,2),(5,5),(8,2)]
  | _ => some [(5,0),(5,3),(7,0),(8,0)]
theorem root7Node24Domains1_fast_eq : root7Node24Domains1 = expandDomains root7Node24Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node24Domains1 v = expandDomains root7Node24Domains1Fast v from by decide) v
theorem root7Node24Step1Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root7Node24Domains0 root7Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains0 root7Node24Domains1
    root7Node24Domains0Fast root7Node24Domains1Fast
    root7Node24Domains0_fast_eq root7Node24Domains1_fast_eq (by decide)
theorem root7Node24Step1_checked :
    checkReplacement table13 root7Node24Domains0 root7Node24Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node24Step1Chunk0_0_checked, root7Node24Step1Chunk0_1_checked, root7Node24Step1Chunk0_2_checked, root7Node24Step1Chunk0_3_checked, root7Node24Step1Chunk0_4_checked, root7Node24Step1Chunk0_5_checked, root7Node24Step1Chunk1_0_checked, root7Node24Step1Chunk1_1_checked, root7Node24Step1Chunk1_2_checked, root7Node24Step1Chunk1_3_checked, root7Node24Step1Chunk1_4_checked, root7Node24Step1Chunk1_5_checked, root7Node24Step1Chunk2_0_checked, root7Node24Step1Chunk2_1_checked, root7Node24Step1Chunk2_2_checked, root7Node24Step1Chunk2_3_checked, root7Node24Step1Chunk2_4_checked, root7Node24Step1Chunk2_5_checked, root7Node24Step1Chunk3_0_checked, root7Node24Step1Chunk3_1_checked, root7Node24Step1Chunk3_2_checked, root7Node24Step1Chunk3_3_checked, root7Node24Step1Chunk3_4_checked, root7Node24Step1Chunk3_5_checked, root7Node24Step1Chunk4_0_checked, root7Node24Step1Chunk4_1_checked, root7Node24Step1Chunk4_2_checked, root7Node24Step1Chunk4_3_checked, root7Node24Step1Chunk4_4_checked, root7Node24Step1Chunk4_5_checked, root7Node24Step1Chunk5_0_checked, root7Node24Step1Chunk5_1_checked, root7Node24Step1Chunk5_2_checked, root7Node24Step1Chunk5_3_checked, root7Node24Step1Chunk5_4_checked, root7Node24Step1Chunk5_5_checked, root7Node24Step1Chunk6_0_checked, root7Node24Step1Chunk6_1_checked, root7Node24Step1Chunk6_2_checked, root7Node24Step1Chunk6_3_checked, root7Node24Step1Chunk6_4_checked, root7Node24Step1Chunk6_5_checked, root7Node24Step1Chunk7_0_checked, root7Node24Step1Chunk7_1_checked, root7Node24Step1Chunk7_2_checked, root7Node24Step1Chunk7_3_checked, root7Node24Step1Chunk7_4_checked, root7Node24Step1Chunk7_5_checked, root7Node24Step1Chunk8_0_checked, root7Node24Step1Chunk8_1_checked, root7Node24Step1Chunk8_2_checked, root7Node24Step1Chunk8_3_checked, root7Node24Step1Chunk8_4_checked, root7Node24Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node24Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0)]
  | 2 => [(4,5)]
  | 3 => [(1,0)]
  | 4 => [(1,2),(6,2)]
  | 5 => [(8,4)]
  | 6 => [(0,0)]
  | 7 => [(7,2)]
  | 8 => [(4,0)]
  | 9 => [(0,3),(1,0)]
  | 10 => [(7,1),(8,1)]
  | 11 => [(1,5)]
  | 12 => [(6,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(4,2),(8,2)]
  | 16 => [(5,0),(5,3)]
  | 17 => [(4,5),(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5),(8,5)]
  | 21 => [(1,0)]
  | 22 => [(1,4),(3,4),(5,4),(7,4)]
  | 23 => [(0,0),(0,5),(6,3)]
  | 24 => [(4,4),(7,2)]
  | 25 => [(1,4),(7,4)]
  | 26 => [(0,5),(1,3),(6,3)]
  | 27 => [(4,4),(7,2),(8,2)]
  | 28 => [(0,2),(1,5),(6,0)]
  | 29 => [(1,1),(6,1),(7,1)]
  | 30 => [(4,1),(7,5),(8,1)]
  | 31 => [(0,2),(6,0),(6,5)]
  | 32 => [(0,4),(1,1),(7,1)]
  | 33 => [(2,0),(4,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(5,2),(5,5),(8,2)]
  | _ => [(5,0),(7,0),(8,0)]
def root7Node24Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(1,0)]
  | 4 => some [(1,2),(6,2)]
  | 5 => some [(8,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(4,0)]
  | 9 => some [(0,3),(1,0)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(5,1)]
  | 14 => some [(0,1)]
  | 15 => some [(4,2),(8,2)]
  | 16 => some [(5,0),(5,3)]
  | 17 => some [(4,5),(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5),(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(1,4),(3,4),(5,4),(7,4)]
  | 23 => some [(0,0),(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(7,4)]
  | 26 => some [(0,5),(1,3),(6,3)]
  | 27 => some [(4,4),(7,2),(8,2)]
  | 28 => some [(0,2),(1,5),(6,0)]
  | 29 => some [(1,1),(6,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(7,1)]
  | 33 => some [(2,0),(4,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5),(8,2)]
  | _ => some [(5,0),(7,0),(8,0)]
theorem root7Node24Domains2_fast_eq : root7Node24Domains2 = expandDomains root7Node24Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node24Domains2 v = expandDomains root7Node24Domains2Fast v from by decide) v
theorem root7Node24Step2Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root7Node24Domains1 root7Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node24Domains1 root7Node24Domains2
    root7Node24Domains1Fast root7Node24Domains2Fast
    root7Node24Domains1_fast_eq root7Node24Domains2_fast_eq (by decide)
theorem root7Node24Step2_checked :
    checkReplacement table25 root7Node24Domains1 root7Node24Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node24Step2Chunk0_0_checked, root7Node24Step2Chunk0_1_checked, root7Node24Step2Chunk0_2_checked, root7Node24Step2Chunk0_3_checked, root7Node24Step2Chunk0_4_checked, root7Node24Step2Chunk0_5_checked, root7Node24Step2Chunk1_0_checked, root7Node24Step2Chunk1_1_checked, root7Node24Step2Chunk1_2_checked, root7Node24Step2Chunk1_3_checked, root7Node24Step2Chunk1_4_checked, root7Node24Step2Chunk1_5_checked, root7Node24Step2Chunk2_0_checked, root7Node24Step2Chunk2_1_checked, root7Node24Step2Chunk2_2_checked, root7Node24Step2Chunk2_3_checked, root7Node24Step2Chunk2_4_checked, root7Node24Step2Chunk2_5_checked, root7Node24Step2Chunk3_0_checked, root7Node24Step2Chunk3_1_checked, root7Node24Step2Chunk3_2_checked, root7Node24Step2Chunk3_3_checked, root7Node24Step2Chunk3_4_checked, root7Node24Step2Chunk3_5_checked, root7Node24Step2Chunk4_0_checked, root7Node24Step2Chunk4_1_checked, root7Node24Step2Chunk4_2_checked, root7Node24Step2Chunk4_3_checked, root7Node24Step2Chunk4_4_checked, root7Node24Step2Chunk4_5_checked, root7Node24Step2Chunk5_0_checked, root7Node24Step2Chunk5_1_checked, root7Node24Step2Chunk5_2_checked, root7Node24Step2Chunk5_3_checked, root7Node24Step2Chunk5_4_checked, root7Node24Step2Chunk5_5_checked, root7Node24Step2Chunk6_0_checked, root7Node24Step2Chunk6_1_checked, root7Node24Step2Chunk6_2_checked, root7Node24Step2Chunk6_3_checked, root7Node24Step2Chunk6_4_checked, root7Node24Step2Chunk6_5_checked, root7Node24Step2Chunk7_0_checked, root7Node24Step2Chunk7_1_checked, root7Node24Step2Chunk7_2_checked, root7Node24Step2Chunk7_3_checked, root7Node24Step2Chunk7_4_checked, root7Node24Step2Chunk7_5_checked, root7Node24Step2Chunk8_0_checked, root7Node24Step2Chunk8_1_checked, root7Node24Step2Chunk8_2_checked, root7Node24Step2Chunk8_3_checked, root7Node24Step2Chunk8_4_checked, root7Node24Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node25Domains0 : Domains 37 State := restrict root7Node24Domains2 4 (1,2)
def root7Node25Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(1,0)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(4,0)]
  | 9 => some [(0,3),(1,0)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(5,1)]
  | 14 => some [(0,1)]
  | 15 => some [(4,2),(8,2)]
  | 16 => some [(5,0),(5,3)]
  | 17 => some [(4,5),(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5),(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(1,4),(3,4),(5,4),(7,4)]
  | 23 => some [(0,0),(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(7,4)]
  | 26 => some [(0,5),(1,3),(6,3)]
  | 27 => some [(4,4),(7,2),(8,2)]
  | 28 => some [(0,2),(1,5),(6,0)]
  | 29 => some [(1,1),(6,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(7,1)]
  | 33 => some [(2,0),(4,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5),(8,2)]
  | _ => some [(5,0),(7,0),(8,0)]
theorem root7Node25Domains0_fast_eq : root7Node25Domains0 = expandDomains root7Node25Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node25Domains0 v = expandDomains root7Node25Domains0Fast v from by decide) v
def root7Node25Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0)]
  | 2 => [(4,5)]
  | 3 => [(1,0)]
  | 4 => [(1,2)]
  | 5 => [(8,4)]
  | 6 => [(0,0)]
  | 7 => [(7,2)]
  | 8 => [(4,0)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(1,5)]
  | 12 => [(6,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5),(8,5)]
  | 21 => [(1,0)]
  | 22 => [(1,4),(3,4),(7,4)]
  | 23 => [(0,5),(6,3)]
  | 24 => [(4,4),(7,2)]
  | 25 => [(1,4),(7,4)]
  | 26 => [(0,5),(1,3),(6,3)]
  | 27 => [(4,4),(7,2),(8,2)]
  | 28 => [(0,2),(6,0)]
  | 29 => [(1,1),(7,1)]
  | 30 => [(4,1),(7,5),(8,1)]
  | 31 => [(0,2),(6,0),(6,5)]
  | 32 => [(0,4),(1,1),(7,1)]
  | 33 => [(2,0),(4,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(5,2),(5,5),(8,2)]
  | _ => [(5,0),(7,0),(8,0)]
def root7Node25Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(1,0)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(4,0)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(5,1)]
  | 14 => some [(0,1)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5),(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(1,4),(3,4),(7,4)]
  | 23 => some [(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(7,4)]
  | 26 => some [(0,5),(1,3),(6,3)]
  | 27 => some [(4,4),(7,2),(8,2)]
  | 28 => some [(0,2),(6,0)]
  | 29 => some [(1,1),(7,1)]
  | 30 => some [(4,1),(7,5),(8,1)]
  | 31 => some [(0,2),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(7,1)]
  | 33 => some [(2,0),(4,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(5,2),(5,5),(8,2)]
  | _ => some [(5,0),(7,0),(8,0)]
theorem root7Node25Domains1_fast_eq : root7Node25Domains1 = expandDomains root7Node25Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node25Domains1 v = expandDomains root7Node25Domains1Fast v from by decide) v
theorem root7Node25Step1Chunk0_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_0⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk0_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_1⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk0_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_2⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk0_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_3⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk0_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_4⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk0_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_5⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk1_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_0⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk1_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_1⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk1_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_2⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk1_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_3⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk1_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_4⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk1_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_5⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk2_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_0⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk2_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_1⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk2_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_2⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk2_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_3⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk2_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_4⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk2_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_5⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk3_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_0⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk3_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_1⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk3_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_2⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk3_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_3⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk3_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_4⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk3_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_5⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk4_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_0⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk4_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_1⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk4_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_2⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk4_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_3⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk4_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_4⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk4_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_5⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk5_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_0⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk5_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_1⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk5_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_2⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk5_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_3⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk5_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_4⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk5_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_5⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk6_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_0⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk6_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_1⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk6_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_2⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk6_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_3⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk6_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_4⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk6_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_5⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk7_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_0⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk7_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_1⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk7_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_2⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk7_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_3⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk7_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_4⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk7_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_5⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk8_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_0⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk8_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_1⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk8_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_2⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk8_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_3⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk8_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_4⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1Chunk8_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_5⟩
      root7Node25Domains0 root7Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node25Domains0 root7Node25Domains1
    root7Node25Domains0Fast root7Node25Domains1Fast
    root7Node25Domains0_fast_eq root7Node25Domains1_fast_eq (by decide)
theorem root7Node25Step1_checked :
    checkReplacement table16 root7Node25Domains0 root7Node25Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node25Step1Chunk0_0_checked, root7Node25Step1Chunk0_1_checked, root7Node25Step1Chunk0_2_checked, root7Node25Step1Chunk0_3_checked, root7Node25Step1Chunk0_4_checked, root7Node25Step1Chunk0_5_checked, root7Node25Step1Chunk1_0_checked, root7Node25Step1Chunk1_1_checked, root7Node25Step1Chunk1_2_checked, root7Node25Step1Chunk1_3_checked, root7Node25Step1Chunk1_4_checked, root7Node25Step1Chunk1_5_checked, root7Node25Step1Chunk2_0_checked, root7Node25Step1Chunk2_1_checked, root7Node25Step1Chunk2_2_checked, root7Node25Step1Chunk2_3_checked, root7Node25Step1Chunk2_4_checked, root7Node25Step1Chunk2_5_checked, root7Node25Step1Chunk3_0_checked, root7Node25Step1Chunk3_1_checked, root7Node25Step1Chunk3_2_checked, root7Node25Step1Chunk3_3_checked, root7Node25Step1Chunk3_4_checked, root7Node25Step1Chunk3_5_checked, root7Node25Step1Chunk4_0_checked, root7Node25Step1Chunk4_1_checked, root7Node25Step1Chunk4_2_checked, root7Node25Step1Chunk4_3_checked, root7Node25Step1Chunk4_4_checked, root7Node25Step1Chunk4_5_checked, root7Node25Step1Chunk5_0_checked, root7Node25Step1Chunk5_1_checked, root7Node25Step1Chunk5_2_checked, root7Node25Step1Chunk5_3_checked, root7Node25Step1Chunk5_4_checked, root7Node25Step1Chunk5_5_checked, root7Node25Step1Chunk6_0_checked, root7Node25Step1Chunk6_1_checked, root7Node25Step1Chunk6_2_checked, root7Node25Step1Chunk6_3_checked, root7Node25Step1Chunk6_4_checked, root7Node25Step1Chunk6_5_checked, root7Node25Step1Chunk7_0_checked, root7Node25Step1Chunk7_1_checked, root7Node25Step1Chunk7_2_checked, root7Node25Step1Chunk7_3_checked, root7Node25Step1Chunk7_4_checked, root7Node25Step1Chunk7_5_checked, root7Node25Step1Chunk8_0_checked, root7Node25Step1Chunk8_1_checked, root7Node25Step1Chunk8_2_checked, root7Node25Step1Chunk8_3_checked, root7Node25Step1Chunk8_4_checked, root7Node25Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
