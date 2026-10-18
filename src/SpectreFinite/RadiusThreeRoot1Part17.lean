module

public import SpectreFinite.RadiusThreeRoot1Part16
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable11
public import SpectreFinite.RadiusThreeTable13
public import SpectreFinite.RadiusThreeTable30

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node30Domains0 : Domains 37 State := restrict root1Node29Domains0 3 (0,3)
def root1Node30Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
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
  | 14 => some [(0,0),(1,3),(6,3),(6,4)]
  | 15 => some [(7,0),(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5),(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(2,1),(7,1)]
  | 20 => some [(0,2),(1,5),(6,5),(7,5)]
  | 21 => some [(0,3),(0,4),(1,1),(6,1)]
  | 22 => some [(1,4),(7,4)]
  | 23 => some [(0,5),(1,3),(6,3)]
  | 24 => some [(4,4),(7,2),(8,2)]
  | 25 => some [(0,0),(4,0),(5,0),(8,0)]
  | 26 => some [(3,2),(4,5),(7,3)]
  | 27 => some [(4,0),(4,2),(7,0)]
  | 28 => some [(0,2),(6,0),(6,5)]
  | 29 => some [(0,4),(1,1),(7,1)]
  | 30 => some [(1,5),(5,1),(5,4)]
  | 31 => some [(0,0),(0,1),(6,1),(6,4)]
  | 32 => some [(1,2),(5,1),(6,2),(7,2)]
  | 33 => some [(5,0),(7,0),(8,0)]
  | 34 => some [(4,3),(4,5),(8,3)]
  | 35 => some [(1,5),(3,5),(5,5),(7,0),(7,5)]
  | _ => some [(0,3),(1,0),(6,1),(8,3)]
theorem root1Node30Domains0_fast_eq : root1Node30Domains0 = expandDomains root1Node30Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node30Domains0 v = expandDomains root1Node30Domains0Fast v from by decide) v
def root1Node30Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(1,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(7,2)]
  | 5 => [(4,0)]
  | 6 => [(7,3)]
  | 7 => [(4,2)]
  | 8 => [(5,3)]
  | 9 => [(1,1),(6,1)]
  | 10 => [(5,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3),(6,3)]
  | 15 => [(7,0),(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5),(8,5)]
  | 18 => [(1,0)]
  | 19 => [(2,1),(7,1)]
  | 20 => [(0,2),(6,5)]
  | 21 => [(0,4),(1,1)]
  | 22 => [(1,4),(7,4)]
  | 23 => [(0,5),(1,3),(6,3)]
  | 24 => [(4,4),(7,2),(8,2)]
  | 25 => [(0,0),(5,0)]
  | 26 => [(3,2),(4,5)]
  | 27 => [(4,0),(7,0)]
  | 28 => [(0,2),(6,0),(6,5)]
  | 29 => [(0,4),(1,1),(7,1)]
  | 30 => [(1,5),(5,1),(5,4)]
  | 31 => [(0,0),(0,1),(6,1),(6,4)]
  | 32 => [(1,2),(5,1),(6,2),(7,2)]
  | 33 => [(5,0),(7,0),(8,0)]
  | 34 => [(4,3),(4,5),(8,3)]
  | 35 => [(1,5),(3,5),(5,5),(7,0),(7,5)]
  | _ => [(0,3),(1,0),(6,1),(8,3)]
def root1Node30Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(7,2)]
  | 5 => some [(4,0)]
  | 6 => some [(7,3)]
  | 7 => some [(4,2)]
  | 8 => some [(5,3)]
  | 9 => some [(1,1),(6,1)]
  | 10 => some [(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3),(6,3)]
  | 15 => some [(7,0),(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5),(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(2,1),(7,1)]
  | 20 => some [(0,2),(6,5)]
  | 21 => some [(0,4),(1,1)]
  | 22 => some [(1,4),(7,4)]
  | 23 => some [(0,5),(1,3),(6,3)]
  | 24 => some [(4,4),(7,2),(8,2)]
  | 25 => some [(0,0),(5,0)]
  | 26 => some [(3,2),(4,5)]
  | 27 => some [(4,0),(7,0)]
  | 28 => some [(0,2),(6,0),(6,5)]
  | 29 => some [(0,4),(1,1),(7,1)]
  | 30 => some [(1,5),(5,1),(5,4)]
  | 31 => some [(0,0),(0,1),(6,1),(6,4)]
  | 32 => some [(1,2),(5,1),(6,2),(7,2)]
  | 33 => some [(5,0),(7,0),(8,0)]
  | 34 => some [(4,3),(4,5),(8,3)]
  | 35 => some [(1,5),(3,5),(5,5),(7,0),(7,5)]
  | _ => some [(0,3),(1,0),(6,1),(8,3)]
theorem root1Node30Domains1_fast_eq : root1Node30Domains1 = expandDomains root1Node30Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node30Domains1 v = expandDomains root1Node30Domains1Fast v from by decide) v
theorem root1Node30Step1Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root1Node30Domains0 root1Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains0 root1Node30Domains1
    root1Node30Domains0Fast root1Node30Domains1Fast
    root1Node30Domains0_fast_eq root1Node30Domains1_fast_eq (by decide)
theorem root1Node30Step1_checked :
    checkReplacement table13 root1Node30Domains0 root1Node30Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node30Step1Chunk0_0_checked, root1Node30Step1Chunk0_1_checked, root1Node30Step1Chunk0_2_checked, root1Node30Step1Chunk0_3_checked, root1Node30Step1Chunk0_4_checked, root1Node30Step1Chunk0_5_checked, root1Node30Step1Chunk1_0_checked, root1Node30Step1Chunk1_1_checked, root1Node30Step1Chunk1_2_checked, root1Node30Step1Chunk1_3_checked, root1Node30Step1Chunk1_4_checked, root1Node30Step1Chunk1_5_checked, root1Node30Step1Chunk2_0_checked, root1Node30Step1Chunk2_1_checked, root1Node30Step1Chunk2_2_checked, root1Node30Step1Chunk2_3_checked, root1Node30Step1Chunk2_4_checked, root1Node30Step1Chunk2_5_checked, root1Node30Step1Chunk3_0_checked, root1Node30Step1Chunk3_1_checked, root1Node30Step1Chunk3_2_checked, root1Node30Step1Chunk3_3_checked, root1Node30Step1Chunk3_4_checked, root1Node30Step1Chunk3_5_checked, root1Node30Step1Chunk4_0_checked, root1Node30Step1Chunk4_1_checked, root1Node30Step1Chunk4_2_checked, root1Node30Step1Chunk4_3_checked, root1Node30Step1Chunk4_4_checked, root1Node30Step1Chunk4_5_checked, root1Node30Step1Chunk5_0_checked, root1Node30Step1Chunk5_1_checked, root1Node30Step1Chunk5_2_checked, root1Node30Step1Chunk5_3_checked, root1Node30Step1Chunk5_4_checked, root1Node30Step1Chunk5_5_checked, root1Node30Step1Chunk6_0_checked, root1Node30Step1Chunk6_1_checked, root1Node30Step1Chunk6_2_checked, root1Node30Step1Chunk6_3_checked, root1Node30Step1Chunk6_4_checked, root1Node30Step1Chunk6_5_checked, root1Node30Step1Chunk7_0_checked, root1Node30Step1Chunk7_1_checked, root1Node30Step1Chunk7_2_checked, root1Node30Step1Chunk7_3_checked, root1Node30Step1Chunk7_4_checked, root1Node30Step1Chunk7_5_checked, root1Node30Step1Chunk8_0_checked, root1Node30Step1Chunk8_1_checked, root1Node30Step1Chunk8_2_checked, root1Node30Step1Chunk8_3_checked, root1Node30Step1Chunk8_4_checked, root1Node30Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node30Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(1,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(7,2)]
  | 5 => [(4,0)]
  | 6 => [(7,3)]
  | 7 => [(4,2)]
  | 8 => [(5,3)]
  | 9 => [(1,1),(6,1)]
  | 10 => [(5,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3),(6,3)]
  | 15 => [(7,0),(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5),(8,5)]
  | 18 => [(1,0)]
  | 19 => [(2,1),(7,1)]
  | 20 => [(0,2),(6,5)]
  | 21 => [(0,4),(1,1)]
  | 22 => [(1,4),(7,4)]
  | 23 => [(0,5),(1,3)]
  | 24 => [(4,4),(8,2)]
  | 25 => [(0,0),(5,0)]
  | 26 => [(3,2),(4,5)]
  | 27 => [(4,0),(7,0)]
  | 28 => [(6,0),(6,5)]
  | 29 => [(0,4),(7,1)]
  | 30 => [(1,5),(5,4)]
  | 31 => [(0,0),(6,1)]
  | 32 => [(5,1),(7,2)]
  | 33 => [(5,0),(7,0)]
  | 34 => [(4,3),(4,5)]
  | 35 => [(1,5),(7,0)]
  | _ => [(6,1),(8,3)]
def root1Node30Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(7,2)]
  | 5 => some [(4,0)]
  | 6 => some [(7,3)]
  | 7 => some [(4,2)]
  | 8 => some [(5,3)]
  | 9 => some [(1,1),(6,1)]
  | 10 => some [(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3),(6,3)]
  | 15 => some [(7,0),(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5),(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(2,1),(7,1)]
  | 20 => some [(0,2),(6,5)]
  | 21 => some [(0,4),(1,1)]
  | 22 => some [(1,4),(7,4)]
  | 23 => some [(0,5),(1,3)]
  | 24 => some [(4,4),(8,2)]
  | 25 => some [(0,0),(5,0)]
  | 26 => some [(3,2),(4,5)]
  | 27 => some [(4,0),(7,0)]
  | 28 => some [(6,0),(6,5)]
  | 29 => some [(0,4),(7,1)]
  | 30 => some [(1,5),(5,4)]
  | 31 => some [(0,0),(6,1)]
  | 32 => some [(5,1),(7,2)]
  | 33 => some [(5,0),(7,0)]
  | 34 => some [(4,3),(4,5)]
  | 35 => some [(1,5),(7,0)]
  | _ => some [(6,1),(8,3)]
theorem root1Node30Domains2_fast_eq : root1Node30Domains2 = expandDomains root1Node30Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node30Domains2 v = expandDomains root1Node30Domains2Fast v from by decide) v
theorem root1Node30Step2Chunk0_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_0⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk0_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_1⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk0_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_2⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk0_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_3⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk0_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_4⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk0_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_5⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk1_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_0⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk1_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_1⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk1_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_2⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk1_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_3⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk1_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_4⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk1_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_5⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk2_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_0⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk2_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_1⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk2_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_2⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk2_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_3⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk2_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_4⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk2_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_5⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk3_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_0⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk3_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_1⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk3_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_2⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk3_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_3⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk3_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_4⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk3_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_5⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk4_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_0⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk4_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_1⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk4_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_2⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk4_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_3⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk4_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_4⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk4_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_5⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk5_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_0⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk5_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_1⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk5_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_2⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk5_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_3⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk5_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_4⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk5_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_5⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk6_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_0⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk6_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_1⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk6_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_2⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk6_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_3⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk6_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_4⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk6_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_5⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk7_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_0⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk7_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_1⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk7_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_2⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk7_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_3⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk7_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_4⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk7_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_5⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk8_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_0⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk8_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_1⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk8_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_2⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk8_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_3⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk8_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_4⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2Chunk8_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_5⟩
      root1Node30Domains1 root1Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains1 root1Node30Domains2
    root1Node30Domains1Fast root1Node30Domains2Fast
    root1Node30Domains1_fast_eq root1Node30Domains2_fast_eq (by decide)
theorem root1Node30Step2_checked :
    checkReplacement table30 root1Node30Domains1 root1Node30Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node30Step2Chunk0_0_checked, root1Node30Step2Chunk0_1_checked, root1Node30Step2Chunk0_2_checked, root1Node30Step2Chunk0_3_checked, root1Node30Step2Chunk0_4_checked, root1Node30Step2Chunk0_5_checked, root1Node30Step2Chunk1_0_checked, root1Node30Step2Chunk1_1_checked, root1Node30Step2Chunk1_2_checked, root1Node30Step2Chunk1_3_checked, root1Node30Step2Chunk1_4_checked, root1Node30Step2Chunk1_5_checked, root1Node30Step2Chunk2_0_checked, root1Node30Step2Chunk2_1_checked, root1Node30Step2Chunk2_2_checked, root1Node30Step2Chunk2_3_checked, root1Node30Step2Chunk2_4_checked, root1Node30Step2Chunk2_5_checked, root1Node30Step2Chunk3_0_checked, root1Node30Step2Chunk3_1_checked, root1Node30Step2Chunk3_2_checked, root1Node30Step2Chunk3_3_checked, root1Node30Step2Chunk3_4_checked, root1Node30Step2Chunk3_5_checked, root1Node30Step2Chunk4_0_checked, root1Node30Step2Chunk4_1_checked, root1Node30Step2Chunk4_2_checked, root1Node30Step2Chunk4_3_checked, root1Node30Step2Chunk4_4_checked, root1Node30Step2Chunk4_5_checked, root1Node30Step2Chunk5_0_checked, root1Node30Step2Chunk5_1_checked, root1Node30Step2Chunk5_2_checked, root1Node30Step2Chunk5_3_checked, root1Node30Step2Chunk5_4_checked, root1Node30Step2Chunk5_5_checked, root1Node30Step2Chunk6_0_checked, root1Node30Step2Chunk6_1_checked, root1Node30Step2Chunk6_2_checked, root1Node30Step2Chunk6_3_checked, root1Node30Step2Chunk6_4_checked, root1Node30Step2Chunk6_5_checked, root1Node30Step2Chunk7_0_checked, root1Node30Step2Chunk7_1_checked, root1Node30Step2Chunk7_2_checked, root1Node30Step2Chunk7_3_checked, root1Node30Step2Chunk7_4_checked, root1Node30Step2Chunk7_5_checked, root1Node30Step2Chunk8_0_checked, root1Node30Step2Chunk8_1_checked, root1Node30Step2Chunk8_2_checked, root1Node30Step2Chunk8_3_checked, root1Node30Step2Chunk8_4_checked, root1Node30Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node30Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(1,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(7,2)]
  | 5 => [(4,0)]
  | 6 => [(7,3)]
  | 7 => [(4,2)]
  | 8 => [(5,3)]
  | 9 => [(1,1),(6,1)]
  | 10 => [(5,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3),(6,3)]
  | 15 => [(7,0),(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(1,0)]
  | 19 => [(2,1)]
  | 20 => [(0,2),(6,5)]
  | 21 => [(0,4),(1,1)]
  | 22 => [(1,4),(7,4)]
  | 23 => [(0,5)]
  | 24 => [(4,4)]
  | 25 => [(0,0)]
  | 26 => [(3,2),(4,5)]
  | 27 => [(4,0),(7,0)]
  | 28 => [(6,0),(6,5)]
  | 29 => [(0,4),(7,1)]
  | 30 => [(1,5),(5,4)]
  | 31 => [(0,0),(6,1)]
  | 32 => [(5,1),(7,2)]
  | 33 => [(5,0),(7,0)]
  | 34 => [(4,3),(4,5)]
  | 35 => [(1,5),(7,0)]
  | _ => [(6,1),(8,3)]
def root1Node30Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(7,2)]
  | 5 => some [(4,0)]
  | 6 => some [(7,3)]
  | 7 => some [(4,2)]
  | 8 => some [(5,3)]
  | 9 => some [(1,1),(6,1)]
  | 10 => some [(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3),(6,3)]
  | 15 => some [(7,0),(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(1,0)]
  | 19 => some [(2,1)]
  | 20 => some [(0,2),(6,5)]
  | 21 => some [(0,4),(1,1)]
  | 22 => some [(1,4),(7,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(0,0)]
  | 26 => some [(3,2),(4,5)]
  | 27 => some [(4,0),(7,0)]
  | 28 => some [(6,0),(6,5)]
  | 29 => some [(0,4),(7,1)]
  | 30 => some [(1,5),(5,4)]
  | 31 => some [(0,0),(6,1)]
  | 32 => some [(5,1),(7,2)]
  | 33 => some [(5,0),(7,0)]
  | 34 => some [(4,3),(4,5)]
  | 35 => some [(1,5),(7,0)]
  | _ => some [(6,1),(8,3)]
theorem root1Node30Domains3_fast_eq : root1Node30Domains3 = expandDomains root1Node30Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node30Domains3 v = expandDomains root1Node30Domains3Fast v from by decide) v
theorem root1Node30Step3Chunk0_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_0⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk0_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_1⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk0_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_2⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk0_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_3⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk0_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_4⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk0_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_5⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk1_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_0⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk1_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_1⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk1_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_2⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk1_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_3⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk1_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_4⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk1_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_5⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk2_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_0⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk2_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_1⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk2_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_2⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk2_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_3⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk2_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_4⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk2_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_5⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk3_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_0⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk3_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_1⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk3_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_2⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk3_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_3⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk3_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_4⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk3_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_5⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk4_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_0⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk4_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_1⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk4_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_2⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk4_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_3⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk4_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_4⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk4_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_5⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk5_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_0⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk5_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_1⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk5_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_2⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk5_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_3⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk5_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_4⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk5_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_5⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk6_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_0⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk6_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_1⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk6_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_2⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk6_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_3⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk6_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_4⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk6_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_5⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk7_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_0⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk7_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_1⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk7_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_2⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk7_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_3⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk7_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_4⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk7_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_5⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk8_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_0⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk8_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_1⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk8_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_2⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk8_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_3⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk8_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_4⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3Chunk8_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_5⟩
      root1Node30Domains2 root1Node30Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node30Domains2 root1Node30Domains3
    root1Node30Domains2Fast root1Node30Domains3Fast
    root1Node30Domains2_fast_eq root1Node30Domains3_fast_eq (by decide)
theorem root1Node30Step3_checked :
    checkReplacement table11 root1Node30Domains2 root1Node30Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node30Step3Chunk0_0_checked, root1Node30Step3Chunk0_1_checked, root1Node30Step3Chunk0_2_checked, root1Node30Step3Chunk0_3_checked, root1Node30Step3Chunk0_4_checked, root1Node30Step3Chunk0_5_checked, root1Node30Step3Chunk1_0_checked, root1Node30Step3Chunk1_1_checked, root1Node30Step3Chunk1_2_checked, root1Node30Step3Chunk1_3_checked, root1Node30Step3Chunk1_4_checked, root1Node30Step3Chunk1_5_checked, root1Node30Step3Chunk2_0_checked, root1Node30Step3Chunk2_1_checked, root1Node30Step3Chunk2_2_checked, root1Node30Step3Chunk2_3_checked, root1Node30Step3Chunk2_4_checked, root1Node30Step3Chunk2_5_checked, root1Node30Step3Chunk3_0_checked, root1Node30Step3Chunk3_1_checked, root1Node30Step3Chunk3_2_checked, root1Node30Step3Chunk3_3_checked, root1Node30Step3Chunk3_4_checked, root1Node30Step3Chunk3_5_checked, root1Node30Step3Chunk4_0_checked, root1Node30Step3Chunk4_1_checked, root1Node30Step3Chunk4_2_checked, root1Node30Step3Chunk4_3_checked, root1Node30Step3Chunk4_4_checked, root1Node30Step3Chunk4_5_checked, root1Node30Step3Chunk5_0_checked, root1Node30Step3Chunk5_1_checked, root1Node30Step3Chunk5_2_checked, root1Node30Step3Chunk5_3_checked, root1Node30Step3Chunk5_4_checked, root1Node30Step3Chunk5_5_checked, root1Node30Step3Chunk6_0_checked, root1Node30Step3Chunk6_1_checked, root1Node30Step3Chunk6_2_checked, root1Node30Step3Chunk6_3_checked, root1Node30Step3Chunk6_4_checked, root1Node30Step3Chunk6_5_checked, root1Node30Step3Chunk7_0_checked, root1Node30Step3Chunk7_1_checked, root1Node30Step3Chunk7_2_checked, root1Node30Step3Chunk7_3_checked, root1Node30Step3Chunk7_4_checked, root1Node30Step3Chunk7_5_checked, root1Node30Step3Chunk8_0_checked, root1Node30Step3Chunk8_1_checked, root1Node30Step3Chunk8_2_checked, root1Node30Step3Chunk8_3_checked, root1Node30Step3Chunk8_4_checked, root1Node30Step3Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
