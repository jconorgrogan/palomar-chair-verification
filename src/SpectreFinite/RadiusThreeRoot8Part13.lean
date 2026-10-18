module

public import SpectreFinite.RadiusThreeRoot8Part12
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
def root8Node22Domains0 : Domains 37 State := restrict root8Node21Domains1 3 (1,0)
def root8Node22Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(4,0),(7,4)]
  | 9 => some [(1,1),(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(4,1),(5,1),(8,1)]
  | 14 => some [(0,1),(0,2),(6,5)]
  | 15 => some [(2,0),(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5)]
  | 21 => some [(1,0),(3,0),(5,0),(7,0)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(1,4),(6,4)]
  | 26 => some [(0,5),(1,2)]
  | 27 => some [(4,4),(8,4)]
  | 28 => some [(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3),(6,0)]
  | 32 => some [(7,1),(8,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(4,2),(8,2)]
  | _ => some [(5,0),(5,3),(8,0)]
theorem root8Node22Domains0_fast_eq : root8Node22Domains0 = expandDomains root8Node22Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node22Domains0 v = expandDomains root8Node22Domains0Fast v from by decide) v
def root8Node22Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,2)]
  | 5 => [(7,4)]
  | 6 => [(6,3)]
  | 7 => [(7,2)]
  | 8 => [(4,0)]
  | 9 => [(1,1),(6,1)]
  | 10 => [(4,1)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(2,0),(4,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(1,0)]
  | 22 => [(0,1)]
  | 23 => [(6,2)]
  | 24 => [(8,4)]
  | 25 => [(1,4)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(1,0)]
  | 29 => [(7,1)]
  | 30 => [(7,5)]
  | 31 => [(0,3),(6,0)]
  | 32 => [(7,1),(8,1)]
  | 33 => [(4,0),(8,0)]
  | 34 => [(7,3)]
  | 35 => [(4,2),(8,2)]
  | _ => [(5,0),(5,3),(8,0)]
def root8Node22Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(4,0)]
  | 9 => some [(1,1),(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(5,1)]
  | 14 => some [(0,1)]
  | 15 => some [(2,0),(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(1,0)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(1,4)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3),(6,0)]
  | 32 => some [(7,1),(8,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(4,2),(8,2)]
  | _ => some [(5,0),(5,3),(8,0)]
theorem root8Node22Domains1_fast_eq : root8Node22Domains1 = expandDomains root8Node22Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node22Domains1 v = expandDomains root8Node22Domains1Fast v from by decide) v
theorem root8Node22Step1Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root8Node22Domains0 root8Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains0 root8Node22Domains1
    root8Node22Domains0Fast root8Node22Domains1Fast
    root8Node22Domains0_fast_eq root8Node22Domains1_fast_eq (by decide)
theorem root8Node22Step1_checked :
    checkReplacement table13 root8Node22Domains0 root8Node22Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node22Step1Chunk0_0_checked, root8Node22Step1Chunk0_1_checked, root8Node22Step1Chunk0_2_checked, root8Node22Step1Chunk0_3_checked, root8Node22Step1Chunk0_4_checked, root8Node22Step1Chunk0_5_checked, root8Node22Step1Chunk1_0_checked, root8Node22Step1Chunk1_1_checked, root8Node22Step1Chunk1_2_checked, root8Node22Step1Chunk1_3_checked, root8Node22Step1Chunk1_4_checked, root8Node22Step1Chunk1_5_checked, root8Node22Step1Chunk2_0_checked, root8Node22Step1Chunk2_1_checked, root8Node22Step1Chunk2_2_checked, root8Node22Step1Chunk2_3_checked, root8Node22Step1Chunk2_4_checked, root8Node22Step1Chunk2_5_checked, root8Node22Step1Chunk3_0_checked, root8Node22Step1Chunk3_1_checked, root8Node22Step1Chunk3_2_checked, root8Node22Step1Chunk3_3_checked, root8Node22Step1Chunk3_4_checked, root8Node22Step1Chunk3_5_checked, root8Node22Step1Chunk4_0_checked, root8Node22Step1Chunk4_1_checked, root8Node22Step1Chunk4_2_checked, root8Node22Step1Chunk4_3_checked, root8Node22Step1Chunk4_4_checked, root8Node22Step1Chunk4_5_checked, root8Node22Step1Chunk5_0_checked, root8Node22Step1Chunk5_1_checked, root8Node22Step1Chunk5_2_checked, root8Node22Step1Chunk5_3_checked, root8Node22Step1Chunk5_4_checked, root8Node22Step1Chunk5_5_checked, root8Node22Step1Chunk6_0_checked, root8Node22Step1Chunk6_1_checked, root8Node22Step1Chunk6_2_checked, root8Node22Step1Chunk6_3_checked, root8Node22Step1Chunk6_4_checked, root8Node22Step1Chunk6_5_checked, root8Node22Step1Chunk7_0_checked, root8Node22Step1Chunk7_1_checked, root8Node22Step1Chunk7_2_checked, root8Node22Step1Chunk7_3_checked, root8Node22Step1Chunk7_4_checked, root8Node22Step1Chunk7_5_checked, root8Node22Step1Chunk8_0_checked, root8Node22Step1Chunk8_1_checked, root8Node22Step1Chunk8_2_checked, root8Node22Step1Chunk8_3_checked, root8Node22Step1Chunk8_4_checked, root8Node22Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node22Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,2)]
  | 5 => [(7,4)]
  | 6 => [(6,3)]
  | 7 => [(7,2)]
  | 8 => [(4,0)]
  | 9 => [(1,1),(6,1)]
  | 10 => [(4,1)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(2,0),(4,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(1,0)]
  | 22 => [(0,1)]
  | 23 => [(6,2)]
  | 24 => [(8,4)]
  | 25 => [(1,4)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(1,0)]
  | 29 => [(7,1)]
  | 30 => [(7,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(4,0),(8,0)]
  | 34 => [(7,3)]
  | 35 => [(8,2)]
  | _ => [(5,0)]
def root8Node22Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(4,0)]
  | 9 => some [(1,1),(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(5,1)]
  | 14 => some [(0,1)]
  | 15 => some [(2,0),(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(1,0)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(1,4)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(8,2)]
  | _ => some [(5,0)]
theorem root8Node22Domains2_fast_eq : root8Node22Domains2 = expandDomains root8Node22Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node22Domains2 v = expandDomains root8Node22Domains2Fast v from by decide) v
theorem root8Node22Step2Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root8Node22Domains1 root8Node22Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node22Domains1 root8Node22Domains2
    root8Node22Domains1Fast root8Node22Domains2Fast
    root8Node22Domains1_fast_eq root8Node22Domains2_fast_eq (by decide)
theorem root8Node22Step2_checked :
    checkReplacement table25 root8Node22Domains1 root8Node22Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node22Step2Chunk0_0_checked, root8Node22Step2Chunk0_1_checked, root8Node22Step2Chunk0_2_checked, root8Node22Step2Chunk0_3_checked, root8Node22Step2Chunk0_4_checked, root8Node22Step2Chunk0_5_checked, root8Node22Step2Chunk1_0_checked, root8Node22Step2Chunk1_1_checked, root8Node22Step2Chunk1_2_checked, root8Node22Step2Chunk1_3_checked, root8Node22Step2Chunk1_4_checked, root8Node22Step2Chunk1_5_checked, root8Node22Step2Chunk2_0_checked, root8Node22Step2Chunk2_1_checked, root8Node22Step2Chunk2_2_checked, root8Node22Step2Chunk2_3_checked, root8Node22Step2Chunk2_4_checked, root8Node22Step2Chunk2_5_checked, root8Node22Step2Chunk3_0_checked, root8Node22Step2Chunk3_1_checked, root8Node22Step2Chunk3_2_checked, root8Node22Step2Chunk3_3_checked, root8Node22Step2Chunk3_4_checked, root8Node22Step2Chunk3_5_checked, root8Node22Step2Chunk4_0_checked, root8Node22Step2Chunk4_1_checked, root8Node22Step2Chunk4_2_checked, root8Node22Step2Chunk4_3_checked, root8Node22Step2Chunk4_4_checked, root8Node22Step2Chunk4_5_checked, root8Node22Step2Chunk5_0_checked, root8Node22Step2Chunk5_1_checked, root8Node22Step2Chunk5_2_checked, root8Node22Step2Chunk5_3_checked, root8Node22Step2Chunk5_4_checked, root8Node22Step2Chunk5_5_checked, root8Node22Step2Chunk6_0_checked, root8Node22Step2Chunk6_1_checked, root8Node22Step2Chunk6_2_checked, root8Node22Step2Chunk6_3_checked, root8Node22Step2Chunk6_4_checked, root8Node22Step2Chunk6_5_checked, root8Node22Step2Chunk7_0_checked, root8Node22Step2Chunk7_1_checked, root8Node22Step2Chunk7_2_checked, root8Node22Step2Chunk7_3_checked, root8Node22Step2Chunk7_4_checked, root8Node22Step2Chunk7_5_checked, root8Node22Step2Chunk8_0_checked, root8Node22Step2Chunk8_1_checked, root8Node22Step2Chunk8_2_checked, root8Node22Step2Chunk8_3_checked, root8Node22Step2Chunk8_4_checked, root8Node22Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node23Domains0 : Domains 37 State := restrict root8Node22Domains2 9 (1,1)
def root8Node23Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(4,0)]
  | 9 => some [(1,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(5,1)]
  | 14 => some [(0,1)]
  | 15 => some [(2,0),(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(1,0)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(1,4)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(4,0),(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(8,2)]
  | _ => some [(5,0)]
theorem root8Node23Domains0_fast_eq : root8Node23Domains0 = expandDomains root8Node23Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node23Domains0 v = expandDomains root8Node23Domains0Fast v from by decide) v
def root8Node23Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,2)]
  | 5 => [(7,4)]
  | 6 => [(6,3)]
  | 7 => [(7,2)]
  | 8 => [(4,0)]
  | 9 => [(1,1)]
  | 10 => [(4,1)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(5,1)]
  | 14 => [(0,1)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(1,0)]
  | 22 => [(0,1)]
  | 23 => [(6,2)]
  | 24 => [(8,4)]
  | 25 => [(1,4)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(1,0)]
  | 29 => [(7,1)]
  | 30 => [(7,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(8,0)]
  | 34 => [(7,3)]
  | 35 => [(8,2)]
  | _ => [(5,0)]
def root8Node23Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(6,3)]
  | 7 => some [(7,2)]
  | 8 => some [(4,0)]
  | 9 => some [(1,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(5,1)]
  | 14 => some [(0,1)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(1,0)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(1,4)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(1,0)]
  | 29 => some [(7,1)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(8,2)]
  | _ => some [(5,0)]
theorem root8Node23Domains1_fast_eq : root8Node23Domains1 = expandDomains root8Node23Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node23Domains1 v = expandDomains root8Node23Domains1Fast v from by decide) v
theorem root8Node23Step1Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root8Node23Domains0 root8Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node23Domains0 root8Node23Domains1
    root8Node23Domains0Fast root8Node23Domains1Fast
    root8Node23Domains0_fast_eq root8Node23Domains1_fast_eq (by decide)
theorem root8Node23Step1_checked :
    checkReplacement table23 root8Node23Domains0 root8Node23Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node23Step1Chunk0_0_checked, root8Node23Step1Chunk0_1_checked, root8Node23Step1Chunk0_2_checked, root8Node23Step1Chunk0_3_checked, root8Node23Step1Chunk0_4_checked, root8Node23Step1Chunk0_5_checked, root8Node23Step1Chunk1_0_checked, root8Node23Step1Chunk1_1_checked, root8Node23Step1Chunk1_2_checked, root8Node23Step1Chunk1_3_checked, root8Node23Step1Chunk1_4_checked, root8Node23Step1Chunk1_5_checked, root8Node23Step1Chunk2_0_checked, root8Node23Step1Chunk2_1_checked, root8Node23Step1Chunk2_2_checked, root8Node23Step1Chunk2_3_checked, root8Node23Step1Chunk2_4_checked, root8Node23Step1Chunk2_5_checked, root8Node23Step1Chunk3_0_checked, root8Node23Step1Chunk3_1_checked, root8Node23Step1Chunk3_2_checked, root8Node23Step1Chunk3_3_checked, root8Node23Step1Chunk3_4_checked, root8Node23Step1Chunk3_5_checked, root8Node23Step1Chunk4_0_checked, root8Node23Step1Chunk4_1_checked, root8Node23Step1Chunk4_2_checked, root8Node23Step1Chunk4_3_checked, root8Node23Step1Chunk4_4_checked, root8Node23Step1Chunk4_5_checked, root8Node23Step1Chunk5_0_checked, root8Node23Step1Chunk5_1_checked, root8Node23Step1Chunk5_2_checked, root8Node23Step1Chunk5_3_checked, root8Node23Step1Chunk5_4_checked, root8Node23Step1Chunk5_5_checked, root8Node23Step1Chunk6_0_checked, root8Node23Step1Chunk6_1_checked, root8Node23Step1Chunk6_2_checked, root8Node23Step1Chunk6_3_checked, root8Node23Step1Chunk6_4_checked, root8Node23Step1Chunk6_5_checked, root8Node23Step1Chunk7_0_checked, root8Node23Step1Chunk7_1_checked, root8Node23Step1Chunk7_2_checked, root8Node23Step1Chunk7_3_checked, root8Node23Step1Chunk7_4_checked, root8Node23Step1Chunk7_5_checked, root8Node23Step1Chunk8_0_checked, root8Node23Step1Chunk8_1_checked, root8Node23Step1Chunk8_2_checked, root8Node23Step1Chunk8_3_checked, root8Node23Step1Chunk8_4_checked, root8Node23Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node23Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node23Domains1 (.output 10) = true := by decide
end SpectreFinite.HexSearch.RadiusThree
