module

public import SpectreFinite.RadiusThreeRoot7Part28
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable0
public import SpectreFinite.RadiusThreeTable17
public import SpectreFinite.RadiusThreeTable19

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node44Domains2 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(3,5),(4,2),(7,0)]
  | 1 => [(0,3),(4,3),(5,3),(8,3)]
  | 2 => [(4,1),(7,5),(8,5)]
  | 3 => [(0,2),(0,3),(1,0),(6,0)]
  | 4 => [(0,5),(1,2),(6,2),(7,2)]
  | 5 => [(2,4),(7,4)]
  | 6 => [(1,3)]
  | 7 => [(4,2),(5,2),(8,2)]
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
  | 32 => [(0,4),(1,1),(3,1),(5,1),(7,1),(8,1)]
  | 33 => [(2,0),(4,0),(7,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | _ => [(3,0),(5,0),(5,3),(7,0),(8,0)]
def root7Node44Domains2Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(3,5),(4,2),(7,0)]
  | 1 => some [(0,3),(4,3),(5,3),(8,3)]
  | 2 => some [(4,1),(7,5),(8,5)]
  | 3 => some [(0,2),(0,3),(1,0),(6,0)]
  | 4 => some [(0,5),(1,2),(6,2),(7,2)]
  | 5 => some [(2,4),(7,4)]
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
  | 32 => some [(0,4),(1,1),(3,1),(5,1),(7,1),(8,1)]
  | 33 => some [(2,0),(4,0),(7,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | _ => some [(3,0),(5,0),(5,3),(7,0),(8,0)]
theorem root7Node44Domains2_fast_eq : root7Node44Domains2 = expandDomains root7Node44Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node44Domains2 v = expandDomains root7Node44Domains2Fast v from by decide) v
theorem root7Node44Step2Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk4_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_0⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk4_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_1⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk4_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_2⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk4_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_3⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk4_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_4⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk4_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_5⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk5_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_0⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk5_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_1⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk5_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_2⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk5_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_3⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk5_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_4⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk5_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_5⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk6_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_0⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk6_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_1⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk6_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_2⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk6_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_3⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk6_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_4⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk6_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_5⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk7_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_0⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk7_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_1⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk7_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_2⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk7_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_3⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk7_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_4⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk7_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_5⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk8_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_0⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk8_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_1⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk8_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_2⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk8_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_3⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk8_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_4⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2Chunk8_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_5⟩
      root7Node44Domains1 root7Node44Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains1 root7Node44Domains2
    root7Node44Domains1Fast root7Node44Domains2Fast
    root7Node44Domains1_fast_eq root7Node44Domains2_fast_eq (by decide)
theorem root7Node44Step2_checked :
    checkReplacement table0 root7Node44Domains1 root7Node44Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node44Step2Chunk0_0_checked, root7Node44Step2Chunk0_1_checked, root7Node44Step2Chunk0_2_checked, root7Node44Step2Chunk0_3_checked, root7Node44Step2Chunk0_4_checked, root7Node44Step2Chunk0_5_checked, root7Node44Step2Chunk1_0_checked, root7Node44Step2Chunk1_1_checked, root7Node44Step2Chunk1_2_checked, root7Node44Step2Chunk1_3_checked, root7Node44Step2Chunk1_4_checked, root7Node44Step2Chunk1_5_checked, root7Node44Step2Chunk2_0_checked, root7Node44Step2Chunk2_1_checked, root7Node44Step2Chunk2_2_checked, root7Node44Step2Chunk2_3_checked, root7Node44Step2Chunk2_4_checked, root7Node44Step2Chunk2_5_checked, root7Node44Step2Chunk3_0_checked, root7Node44Step2Chunk3_1_checked, root7Node44Step2Chunk3_2_checked, root7Node44Step2Chunk3_3_checked, root7Node44Step2Chunk3_4_checked, root7Node44Step2Chunk3_5_checked, root7Node44Step2Chunk4_0_checked, root7Node44Step2Chunk4_1_checked, root7Node44Step2Chunk4_2_checked, root7Node44Step2Chunk4_3_checked, root7Node44Step2Chunk4_4_checked, root7Node44Step2Chunk4_5_checked, root7Node44Step2Chunk5_0_checked, root7Node44Step2Chunk5_1_checked, root7Node44Step2Chunk5_2_checked, root7Node44Step2Chunk5_3_checked, root7Node44Step2Chunk5_4_checked, root7Node44Step2Chunk5_5_checked, root7Node44Step2Chunk6_0_checked, root7Node44Step2Chunk6_1_checked, root7Node44Step2Chunk6_2_checked, root7Node44Step2Chunk6_3_checked, root7Node44Step2Chunk6_4_checked, root7Node44Step2Chunk6_5_checked, root7Node44Step2Chunk7_0_checked, root7Node44Step2Chunk7_1_checked, root7Node44Step2Chunk7_2_checked, root7Node44Step2Chunk7_3_checked, root7Node44Step2Chunk7_4_checked, root7Node44Step2Chunk7_5_checked, root7Node44Step2Chunk8_0_checked, root7Node44Step2Chunk8_1_checked, root7Node44Step2Chunk8_2_checked, root7Node44Step2Chunk8_3_checked, root7Node44Step2Chunk8_4_checked, root7Node44Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node44Domains3 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(3,5),(4,2),(7,0)]
  | 1 => [(0,3),(4,3),(5,3),(8,3)]
  | 2 => [(4,1),(7,5),(8,5)]
  | 3 => [(0,2),(0,3),(1,0),(6,0)]
  | 4 => [(0,5),(1,2),(6,2),(7,2)]
  | 5 => [(2,4),(7,4)]
  | 6 => [(1,3)]
  | 7 => [(4,2),(5,2),(8,2)]
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
def root7Node44Domains3Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(3,5),(4,2),(7,0)]
  | 1 => some [(0,3),(4,3),(5,3),(8,3)]
  | 2 => some [(4,1),(7,5),(8,5)]
  | 3 => some [(0,2),(0,3),(1,0),(6,0)]
  | 4 => some [(0,5),(1,2),(6,2),(7,2)]
  | 5 => some [(2,4),(7,4)]
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
theorem root7Node44Domains3_fast_eq : root7Node44Domains3 = expandDomains root7Node44Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node44Domains3 v = expandDomains root7Node44Domains3Fast v from by decide) v
theorem root7Node44Step3Chunk0_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_0⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk0_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_1⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk0_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_2⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk0_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_3⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk0_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_4⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk0_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_5⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk1_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_0⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk1_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_1⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk1_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_2⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk1_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_3⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk1_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_4⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk1_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_5⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk2_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_0⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk2_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_1⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk2_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_2⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk2_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_3⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk2_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_4⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk2_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_5⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk3_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_0⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk3_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_1⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk3_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_2⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk3_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_3⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk3_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_4⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk3_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_5⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk4_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_0⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk4_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_1⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk4_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_2⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk4_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_3⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk4_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_4⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk4_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_5⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk5_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_0⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk5_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_1⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk5_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_2⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk5_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_3⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk5_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_4⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk5_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_5⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk6_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_0⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk6_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_1⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk6_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_2⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk6_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_3⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk6_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_4⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk6_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_5⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk7_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_0⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk7_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_1⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk7_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_2⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk7_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_3⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk7_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_4⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk7_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_5⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk8_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_0⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk8_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_1⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk8_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_2⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk8_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_3⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk8_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_4⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3Chunk8_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_5⟩
      root7Node44Domains2 root7Node44Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains2 root7Node44Domains3
    root7Node44Domains2Fast root7Node44Domains3Fast
    root7Node44Domains2_fast_eq root7Node44Domains3_fast_eq (by decide)
theorem root7Node44Step3_checked :
    checkReplacement table19 root7Node44Domains2 root7Node44Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node44Step3Chunk0_0_checked, root7Node44Step3Chunk0_1_checked, root7Node44Step3Chunk0_2_checked, root7Node44Step3Chunk0_3_checked, root7Node44Step3Chunk0_4_checked, root7Node44Step3Chunk0_5_checked, root7Node44Step3Chunk1_0_checked, root7Node44Step3Chunk1_1_checked, root7Node44Step3Chunk1_2_checked, root7Node44Step3Chunk1_3_checked, root7Node44Step3Chunk1_4_checked, root7Node44Step3Chunk1_5_checked, root7Node44Step3Chunk2_0_checked, root7Node44Step3Chunk2_1_checked, root7Node44Step3Chunk2_2_checked, root7Node44Step3Chunk2_3_checked, root7Node44Step3Chunk2_4_checked, root7Node44Step3Chunk2_5_checked, root7Node44Step3Chunk3_0_checked, root7Node44Step3Chunk3_1_checked, root7Node44Step3Chunk3_2_checked, root7Node44Step3Chunk3_3_checked, root7Node44Step3Chunk3_4_checked, root7Node44Step3Chunk3_5_checked, root7Node44Step3Chunk4_0_checked, root7Node44Step3Chunk4_1_checked, root7Node44Step3Chunk4_2_checked, root7Node44Step3Chunk4_3_checked, root7Node44Step3Chunk4_4_checked, root7Node44Step3Chunk4_5_checked, root7Node44Step3Chunk5_0_checked, root7Node44Step3Chunk5_1_checked, root7Node44Step3Chunk5_2_checked, root7Node44Step3Chunk5_3_checked, root7Node44Step3Chunk5_4_checked, root7Node44Step3Chunk5_5_checked, root7Node44Step3Chunk6_0_checked, root7Node44Step3Chunk6_1_checked, root7Node44Step3Chunk6_2_checked, root7Node44Step3Chunk6_3_checked, root7Node44Step3Chunk6_4_checked, root7Node44Step3Chunk6_5_checked, root7Node44Step3Chunk7_0_checked, root7Node44Step3Chunk7_1_checked, root7Node44Step3Chunk7_2_checked, root7Node44Step3Chunk7_3_checked, root7Node44Step3Chunk7_4_checked, root7Node44Step3Chunk7_5_checked, root7Node44Step3Chunk8_0_checked, root7Node44Step3Chunk8_1_checked, root7Node44Step3Chunk8_2_checked, root7Node44Step3Chunk8_3_checked, root7Node44Step3Chunk8_4_checked, root7Node44Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node45Domains0 : Domains 37 State := restrict root7Node44Domains3 5 (2,4)
def root7Node45Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(3,5),(4,2),(7,0)]
  | 1 => some [(0,3),(4,3),(5,3),(8,3)]
  | 2 => some [(4,1),(7,5),(8,5)]
  | 3 => some [(0,2),(0,3),(1,0),(6,0)]
  | 4 => some [(0,5),(1,2),(6,2),(7,2)]
  | 5 => some [(2,4)]
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
theorem root7Node45Domains0_fast_eq : root7Node45Domains0 = expandDomains root7Node45Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node45Domains0 v = expandDomains root7Node45Domains0Fast v from by decide) v
def root7Node45Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(3,5),(4,2),(7,0)]
  | 1 => [(0,3),(4,3),(5,3),(8,3)]
  | 2 => [(4,1),(7,5),(8,5)]
  | 3 => [(0,2),(0,3),(1,0),(6,0)]
  | 4 => [(0,5)]
  | 5 => [(2,4)]
  | 6 => [(1,3)]
  | 7 => [(4,2),(5,2),(8,2)]
  | 8 => [(5,0),(5,3),(8,0)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(3,4),(5,4)]
  | 14 => [(0,0),(1,4),(6,3),(6,4)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(0,2),(1,5),(3,5),(7,5)]
  | 21 => [(0,3),(1,1),(6,0),(6,1)]
  | 22 => [(8,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(7,4)]
  | 26 => [(0,5),(1,2),(1,3),(6,3)]
  | 27 => [(2,0),(2,2),(2,4),(4,0),(4,2),(7,2),(8,2)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(4,1),(8,1)]
  | 31 => [(0,2),(0,3),(6,0),(6,5)]
  | 32 => [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 33 => [(2,0),(4,0),(7,0),(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | _ => [(3,0),(5,0),(5,3),(7,0),(8,0)]
def root7Node45Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(3,5),(4,2),(7,0)]
  | 1 => some [(0,3),(4,3),(5,3),(8,3)]
  | 2 => some [(4,1),(7,5),(8,5)]
  | 3 => some [(0,2),(0,3),(1,0),(6,0)]
  | 4 => some [(0,5)]
  | 5 => some [(2,4)]
  | 6 => some [(1,3)]
  | 7 => some [(4,2),(5,2),(8,2)]
  | 8 => some [(5,0),(5,3),(8,0)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(3,4),(5,4)]
  | 14 => some [(0,0),(1,4),(6,3),(6,4)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(0,2),(1,5),(3,5),(7,5)]
  | 21 => some [(0,3),(1,1),(6,0),(6,1)]
  | 22 => some [(8,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(0,5),(1,2),(1,3),(6,3)]
  | 27 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(7,2),(8,2)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(4,1),(8,1)]
  | 31 => some [(0,2),(0,3),(6,0),(6,5)]
  | 32 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 33 => some [(2,0),(4,0),(7,0),(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | _ => some [(3,0),(5,0),(5,3),(7,0),(8,0)]
theorem root7Node45Domains1_fast_eq : root7Node45Domains1 = expandDomains root7Node45Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node45Domains1 v = expandDomains root7Node45Domains1Fast v from by decide) v
theorem root7Node45Step1Chunk0_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_0⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk0_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_1⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk0_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_2⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk0_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_3⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk0_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_4⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk0_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_5⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk1_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_0⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk1_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_1⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk1_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_2⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk1_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_3⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk1_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_4⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk1_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_5⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk2_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_0⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk2_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_1⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk2_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_2⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk2_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_3⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk2_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_4⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk2_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_5⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk3_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_0⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk3_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_1⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk3_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_2⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk3_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_3⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk3_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_4⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk3_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_5⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk4_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_0⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk4_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_1⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk4_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_2⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk4_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_3⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk4_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_4⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk4_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_5⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk5_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_0⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk5_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_1⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk5_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_2⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk5_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_3⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk5_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_4⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk5_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_5⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk6_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_0⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk6_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_1⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk6_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_2⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk6_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_3⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk6_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_4⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk6_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_5⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk7_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_0⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk7_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_1⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk7_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_2⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk7_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_3⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk7_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_4⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk7_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_5⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk8_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_0⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk8_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_1⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk8_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_2⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk8_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_3⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk8_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_4⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1Chunk8_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_5⟩
      root7Node45Domains0 root7Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node45Domains0 root7Node45Domains1
    root7Node45Domains0Fast root7Node45Domains1Fast
    root7Node45Domains0_fast_eq root7Node45Domains1_fast_eq (by decide)
theorem root7Node45Step1_checked :
    checkReplacement table17 root7Node45Domains0 root7Node45Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node45Step1Chunk0_0_checked, root7Node45Step1Chunk0_1_checked, root7Node45Step1Chunk0_2_checked, root7Node45Step1Chunk0_3_checked, root7Node45Step1Chunk0_4_checked, root7Node45Step1Chunk0_5_checked, root7Node45Step1Chunk1_0_checked, root7Node45Step1Chunk1_1_checked, root7Node45Step1Chunk1_2_checked, root7Node45Step1Chunk1_3_checked, root7Node45Step1Chunk1_4_checked, root7Node45Step1Chunk1_5_checked, root7Node45Step1Chunk2_0_checked, root7Node45Step1Chunk2_1_checked, root7Node45Step1Chunk2_2_checked, root7Node45Step1Chunk2_3_checked, root7Node45Step1Chunk2_4_checked, root7Node45Step1Chunk2_5_checked, root7Node45Step1Chunk3_0_checked, root7Node45Step1Chunk3_1_checked, root7Node45Step1Chunk3_2_checked, root7Node45Step1Chunk3_3_checked, root7Node45Step1Chunk3_4_checked, root7Node45Step1Chunk3_5_checked, root7Node45Step1Chunk4_0_checked, root7Node45Step1Chunk4_1_checked, root7Node45Step1Chunk4_2_checked, root7Node45Step1Chunk4_3_checked, root7Node45Step1Chunk4_4_checked, root7Node45Step1Chunk4_5_checked, root7Node45Step1Chunk5_0_checked, root7Node45Step1Chunk5_1_checked, root7Node45Step1Chunk5_2_checked, root7Node45Step1Chunk5_3_checked, root7Node45Step1Chunk5_4_checked, root7Node45Step1Chunk5_5_checked, root7Node45Step1Chunk6_0_checked, root7Node45Step1Chunk6_1_checked, root7Node45Step1Chunk6_2_checked, root7Node45Step1Chunk6_3_checked, root7Node45Step1Chunk6_4_checked, root7Node45Step1Chunk6_5_checked, root7Node45Step1Chunk7_0_checked, root7Node45Step1Chunk7_1_checked, root7Node45Step1Chunk7_2_checked, root7Node45Step1Chunk7_3_checked, root7Node45Step1Chunk7_4_checked, root7Node45Step1Chunk7_5_checked, root7Node45Step1Chunk8_0_checked, root7Node45Step1Chunk8_1_checked, root7Node45Step1Chunk8_2_checked, root7Node45Step1Chunk8_3_checked, root7Node45Step1Chunk8_4_checked, root7Node45Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
