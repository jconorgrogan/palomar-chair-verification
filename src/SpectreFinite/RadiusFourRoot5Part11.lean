module

public import SpectreFinite.RadiusFourRoot5Part10
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable35
public import SpectreFinite.RadiusFourTable36
public import SpectreFinite.RadiusFourTable39
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node31Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(5,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(3,5)]
  | 9 => [(0,3)]
  | 10 => [(4,1)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(2,4)]
  | 16 => [(1,3)]
  | 17 => [(5,2)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(6,5)]
  | 24 => [(0,4)]
  | 25 => [(5,4)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(4,3)]
  | 34 => [(7,5)]
  | 35 => [(5,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(1,3)]
  | 43 => [(8,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(8,1)]
  | 49 => [(6,5)]
  | 50 => [(8,2)]
  | 51 => [(5,0)]
  | 52 => [(4,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(8,5)]
  | 56 => [(5,4)]
  | 57 => [(0,0)]
  | 58 => [(7,2)]
  | 59 => [(7,4)]
  | _ => [(6,3)]
def root5Node31Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(3,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,4)]
  | 16 => some [(1,3)]
  | 17 => some [(5,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(6,5)]
  | 24 => some [(0,4)]
  | 25 => some [(5,4)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(7,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(8,2)]
  | 51 => some [(5,0)]
  | 52 => some [(4,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,4)]
  | 57 => some [(0,0)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root5Node31Domains2_fast_eq : root5Node31Domains2 = expandDomains root5Node31Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node31Domains2 v = expandDomains root5Node31Domains2Fast v from by decide) v
theorem root5Node31Step2Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root5Node31Domains1 root5Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains1 root5Node31Domains2
    root5Node31Domains1Fast root5Node31Domains2Fast
    root5Node31Domains1_fast_eq root5Node31Domains2_fast_eq (by decide)
theorem root5Node31Step2_checked :
    checkReplacement table39 root5Node31Domains1 root5Node31Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node31Step2Chunk0_0_checked, root5Node31Step2Chunk0_1_checked, root5Node31Step2Chunk0_2_checked, root5Node31Step2Chunk0_3_checked, root5Node31Step2Chunk0_4_checked, root5Node31Step2Chunk0_5_checked, root5Node31Step2Chunk1_0_checked, root5Node31Step2Chunk1_1_checked, root5Node31Step2Chunk1_2_checked, root5Node31Step2Chunk1_3_checked, root5Node31Step2Chunk1_4_checked, root5Node31Step2Chunk1_5_checked, root5Node31Step2Chunk2_0_checked, root5Node31Step2Chunk2_1_checked, root5Node31Step2Chunk2_2_checked, root5Node31Step2Chunk2_3_checked, root5Node31Step2Chunk2_4_checked, root5Node31Step2Chunk2_5_checked, root5Node31Step2Chunk3_0_checked, root5Node31Step2Chunk3_1_checked, root5Node31Step2Chunk3_2_checked, root5Node31Step2Chunk3_3_checked, root5Node31Step2Chunk3_4_checked, root5Node31Step2Chunk3_5_checked, root5Node31Step2Chunk4_0_checked, root5Node31Step2Chunk4_1_checked, root5Node31Step2Chunk4_2_checked, root5Node31Step2Chunk4_3_checked, root5Node31Step2Chunk4_4_checked, root5Node31Step2Chunk4_5_checked, root5Node31Step2Chunk5_0_checked, root5Node31Step2Chunk5_1_checked, root5Node31Step2Chunk5_2_checked, root5Node31Step2Chunk5_3_checked, root5Node31Step2Chunk5_4_checked, root5Node31Step2Chunk5_5_checked, root5Node31Step2Chunk6_0_checked, root5Node31Step2Chunk6_1_checked, root5Node31Step2Chunk6_2_checked, root5Node31Step2Chunk6_3_checked, root5Node31Step2Chunk6_4_checked, root5Node31Step2Chunk6_5_checked, root5Node31Step2Chunk7_0_checked, root5Node31Step2Chunk7_1_checked, root5Node31Step2Chunk7_2_checked, root5Node31Step2Chunk7_3_checked, root5Node31Step2Chunk7_4_checked, root5Node31Step2Chunk7_5_checked, root5Node31Step2Chunk8_0_checked, root5Node31Step2Chunk8_1_checked, root5Node31Step2Chunk8_2_checked, root5Node31Step2Chunk8_3_checked, root5Node31Step2Chunk8_4_checked, root5Node31Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root5Node31Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node31Domains2 (.output 14) = true := by decide
def root5Node32Domains0 : Domains 61 State := restrict root5Node30Domains2 26 (8,2)
def root5Node32Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(3,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,4)]
  | 16 => some [(1,3)]
  | 17 => some [(5,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(6,5)]
  | 24 => some [(0,4)]
  | 25 => some [(5,4)]
  | 26 => some [(8,2)]
  | 27 => some [(4,0),(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(7,5)]
  | 35 => some [(5,1),(5,4),(8,4)]
  | 36 => some [(0,1),(6,4)]
  | 37 => some [(1,2),(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(7,5),(8,5)]
  | 44 => some [(0,3),(1,0)]
  | 45 => some [(7,1),(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(4,2),(8,2)]
  | 51 => some [(5,0),(5,3)]
  | 52 => some [(4,5),(5,5),(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4),(5,4),(7,4)]
  | 57 => some [(0,0),(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root5Node32Domains0_fast_eq : root5Node32Domains0 = expandDomains root5Node32Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node32Domains0 v = expandDomains root5Node32Domains0Fast v from by decide) v
def root5Node32Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(5,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(3,5)]
  | 9 => [(0,3)]
  | 10 => [(4,1)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(2,4)]
  | 16 => [(1,3)]
  | 17 => [(5,2)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(6,5)]
  | 24 => [(0,4)]
  | 25 => [(5,4)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(4,3)]
  | 34 => [(7,5)]
  | 35 => [(5,4),(8,4)]
  | 36 => [(6,4)]
  | 37 => [(1,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(1,3)]
  | 43 => [(7,5)]
  | 44 => [(0,3)]
  | 45 => [(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(8,1)]
  | 49 => [(6,5)]
  | 50 => [(4,2)]
  | 51 => [(5,3)]
  | 52 => [(5,5),(8,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(5,5),(8,5)]
  | 56 => [(1,4),(3,4),(7,4)]
  | 57 => [(0,5),(6,3)]
  | 58 => [(4,4),(7,2)]
  | 59 => [(1,4),(7,4)]
  | _ => [(0,5),(6,3)]
def root5Node32Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(3,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,4)]
  | 16 => some [(1,3)]
  | 17 => some [(5,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(6,5)]
  | 24 => some [(0,4)]
  | 25 => some [(5,4)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(7,5)]
  | 35 => some [(5,4),(8,4)]
  | 36 => some [(6,4)]
  | 37 => some [(1,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(7,5)]
  | 44 => some [(0,3)]
  | 45 => some [(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(4,2)]
  | 51 => some [(5,3)]
  | 52 => some [(5,5),(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4),(7,4)]
  | 57 => some [(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root5Node32Domains1_fast_eq : root5Node32Domains1 = expandDomains root5Node32Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node32Domains1 v = expandDomains root5Node32Domains1Fast v from by decide) v
theorem root5Node32Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root5Node32Domains0 root5Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node32Domains0 root5Node32Domains1
    root5Node32Domains0Fast root5Node32Domains1Fast
    root5Node32Domains0_fast_eq root5Node32Domains1_fast_eq (by decide)
theorem root5Node32Step1_checked :
    checkReplacement table36 root5Node32Domains0 root5Node32Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node32Step1Chunk0_0_checked, root5Node32Step1Chunk0_1_checked, root5Node32Step1Chunk0_2_checked, root5Node32Step1Chunk0_3_checked, root5Node32Step1Chunk0_4_checked, root5Node32Step1Chunk0_5_checked, root5Node32Step1Chunk1_0_checked, root5Node32Step1Chunk1_1_checked, root5Node32Step1Chunk1_2_checked, root5Node32Step1Chunk1_3_checked, root5Node32Step1Chunk1_4_checked, root5Node32Step1Chunk1_5_checked, root5Node32Step1Chunk2_0_checked, root5Node32Step1Chunk2_1_checked, root5Node32Step1Chunk2_2_checked, root5Node32Step1Chunk2_3_checked, root5Node32Step1Chunk2_4_checked, root5Node32Step1Chunk2_5_checked, root5Node32Step1Chunk3_0_checked, root5Node32Step1Chunk3_1_checked, root5Node32Step1Chunk3_2_checked, root5Node32Step1Chunk3_3_checked, root5Node32Step1Chunk3_4_checked, root5Node32Step1Chunk3_5_checked, root5Node32Step1Chunk4_0_checked, root5Node32Step1Chunk4_1_checked, root5Node32Step1Chunk4_2_checked, root5Node32Step1Chunk4_3_checked, root5Node32Step1Chunk4_4_checked, root5Node32Step1Chunk4_5_checked, root5Node32Step1Chunk5_0_checked, root5Node32Step1Chunk5_1_checked, root5Node32Step1Chunk5_2_checked, root5Node32Step1Chunk5_3_checked, root5Node32Step1Chunk5_4_checked, root5Node32Step1Chunk5_5_checked, root5Node32Step1Chunk6_0_checked, root5Node32Step1Chunk6_1_checked, root5Node32Step1Chunk6_2_checked, root5Node32Step1Chunk6_3_checked, root5Node32Step1Chunk6_4_checked, root5Node32Step1Chunk6_5_checked, root5Node32Step1Chunk7_0_checked, root5Node32Step1Chunk7_1_checked, root5Node32Step1Chunk7_2_checked, root5Node32Step1Chunk7_3_checked, root5Node32Step1Chunk7_4_checked, root5Node32Step1Chunk7_5_checked, root5Node32Step1Chunk8_0_checked, root5Node32Step1Chunk8_1_checked, root5Node32Step1Chunk8_2_checked, root5Node32Step1Chunk8_3_checked, root5Node32Step1Chunk8_4_checked, root5Node32Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node33Domains0 : Domains 61 State := restrict root5Node32Domains1 35 (5,4)
def root5Node33Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(3,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,4)]
  | 16 => some [(1,3)]
  | 17 => some [(5,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(6,5)]
  | 24 => some [(0,4)]
  | 25 => some [(5,4)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(7,5)]
  | 35 => some [(5,4)]
  | 36 => some [(6,4)]
  | 37 => some [(1,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(7,5)]
  | 44 => some [(0,3)]
  | 45 => some [(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(4,2)]
  | 51 => some [(5,3)]
  | 52 => some [(5,5),(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4),(7,4)]
  | 57 => some [(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root5Node33Domains0_fast_eq : root5Node33Domains0 = expandDomains root5Node33Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node33Domains0 v = expandDomains root5Node33Domains0Fast v from by decide) v
def root5Node33Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(5,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(3,5)]
  | 9 => [(0,3)]
  | 10 => [(4,1)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(2,4)]
  | 16 => [(1,3)]
  | 17 => [(5,2)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(6,5)]
  | 24 => [(0,4)]
  | 25 => [(5,4)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(4,3)]
  | 34 => [(7,5)]
  | 35 => [(5,4)]
  | 36 => [(6,4)]
  | 37 => [(1,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(1,3)]
  | 43 => [(7,5)]
  | 44 => [(0,3)]
  | 45 => [(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(8,1)]
  | 49 => [(6,5)]
  | 50 => [(4,2)]
  | 51 => [(5,3)]
  | 52 => [(5,5),(8,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(5,5),(8,5)]
  | 56 => [(1,4),(3,4)]
  | 57 => [(0,5),(6,3)]
  | 58 => [(4,4),(7,2)]
  | 59 => [(1,4),(7,4)]
  | _ => [(0,5),(6,3)]
def root5Node33Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(3,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,4)]
  | 16 => some [(1,3)]
  | 17 => some [(5,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(6,5)]
  | 24 => some [(0,4)]
  | 25 => some [(5,4)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(7,5)]
  | 35 => some [(5,4)]
  | 36 => some [(6,4)]
  | 37 => some [(1,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(7,5)]
  | 44 => some [(0,3)]
  | 45 => some [(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(4,2)]
  | 51 => some [(5,3)]
  | 52 => some [(5,5),(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4)]
  | 57 => some [(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root5Node33Domains1_fast_eq : root5Node33Domains1 = expandDomains root5Node33Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node33Domains1 v = expandDomains root5Node33Domains1Fast v from by decide) v
theorem root5Node33Step1Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root5Node33Domains0 root5Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node33Domains0 root5Node33Domains1
    root5Node33Domains0Fast root5Node33Domains1Fast
    root5Node33Domains0_fast_eq root5Node33Domains1_fast_eq (by decide)
theorem root5Node33Step1_checked :
    checkReplacement table35 root5Node33Domains0 root5Node33Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node33Step1Chunk0_0_checked, root5Node33Step1Chunk0_1_checked, root5Node33Step1Chunk0_2_checked, root5Node33Step1Chunk0_3_checked, root5Node33Step1Chunk0_4_checked, root5Node33Step1Chunk0_5_checked, root5Node33Step1Chunk1_0_checked, root5Node33Step1Chunk1_1_checked, root5Node33Step1Chunk1_2_checked, root5Node33Step1Chunk1_3_checked, root5Node33Step1Chunk1_4_checked, root5Node33Step1Chunk1_5_checked, root5Node33Step1Chunk2_0_checked, root5Node33Step1Chunk2_1_checked, root5Node33Step1Chunk2_2_checked, root5Node33Step1Chunk2_3_checked, root5Node33Step1Chunk2_4_checked, root5Node33Step1Chunk2_5_checked, root5Node33Step1Chunk3_0_checked, root5Node33Step1Chunk3_1_checked, root5Node33Step1Chunk3_2_checked, root5Node33Step1Chunk3_3_checked, root5Node33Step1Chunk3_4_checked, root5Node33Step1Chunk3_5_checked, root5Node33Step1Chunk4_0_checked, root5Node33Step1Chunk4_1_checked, root5Node33Step1Chunk4_2_checked, root5Node33Step1Chunk4_3_checked, root5Node33Step1Chunk4_4_checked, root5Node33Step1Chunk4_5_checked, root5Node33Step1Chunk5_0_checked, root5Node33Step1Chunk5_1_checked, root5Node33Step1Chunk5_2_checked, root5Node33Step1Chunk5_3_checked, root5Node33Step1Chunk5_4_checked, root5Node33Step1Chunk5_5_checked, root5Node33Step1Chunk6_0_checked, root5Node33Step1Chunk6_1_checked, root5Node33Step1Chunk6_2_checked, root5Node33Step1Chunk6_3_checked, root5Node33Step1Chunk6_4_checked, root5Node33Step1Chunk6_5_checked, root5Node33Step1Chunk7_0_checked, root5Node33Step1Chunk7_1_checked, root5Node33Step1Chunk7_2_checked, root5Node33Step1Chunk7_3_checked, root5Node33Step1Chunk7_4_checked, root5Node33Step1Chunk7_5_checked, root5Node33Step1Chunk8_0_checked, root5Node33Step1Chunk8_1_checked, root5Node33Step1Chunk8_2_checked, root5Node33Step1Chunk8_3_checked, root5Node33Step1Chunk8_4_checked, root5Node33Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node34Domains0 : Domains 61 State := restrict root5Node33Domains1 52 (5,5)
def root5Node34Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(3,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,4)]
  | 16 => some [(1,3)]
  | 17 => some [(5,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(6,5)]
  | 24 => some [(0,4)]
  | 25 => some [(5,4)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(7,5)]
  | 35 => some [(5,4)]
  | 36 => some [(6,4)]
  | 37 => some [(1,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(7,5)]
  | 44 => some [(0,3)]
  | 45 => some [(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(4,2)]
  | 51 => some [(5,3)]
  | 52 => some [(5,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4)]
  | 57 => some [(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root5Node34Domains0_fast_eq : root5Node34Domains0 = expandDomains root5Node34Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node34Domains0 v = expandDomains root5Node34Domains0Fast v from by decide) v
def root5Node34Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(5,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(3,5)]
  | 9 => [(0,3)]
  | 10 => [(4,1)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(2,4)]
  | 16 => [(1,3)]
  | 17 => [(5,2)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(6,5)]
  | 24 => [(0,4)]
  | 25 => [(5,4)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(4,3)]
  | 34 => [(7,5)]
  | 35 => [(5,4)]
  | 36 => [(6,4)]
  | 37 => [(1,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(1,3)]
  | 43 => [(7,5)]
  | 44 => [(0,3)]
  | 45 => [(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(8,1)]
  | 49 => [(6,5)]
  | 50 => [(4,2)]
  | 51 => [(5,3)]
  | 52 => [(5,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(5,5)]
  | 56 => [(1,4)]
  | 57 => [(0,5)]
  | 58 => [(4,4)]
  | 59 => [(1,4)]
  | _ => [(0,5)]
def root5Node34Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(3,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,4)]
  | 16 => some [(1,3)]
  | 17 => some [(5,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(6,5)]
  | 24 => some [(0,4)]
  | 25 => some [(5,4)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(7,5)]
  | 35 => some [(5,4)]
  | 36 => some [(6,4)]
  | 37 => some [(1,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(7,5)]
  | 44 => some [(0,3)]
  | 45 => some [(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(4,2)]
  | 51 => some [(5,3)]
  | 52 => some [(5,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(1,4)]
  | _ => some [(0,5)]
theorem root5Node34Domains1_fast_eq : root5Node34Domains1 = expandDomains root5Node34Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node34Domains1 v = expandDomains root5Node34Domains1Fast v from by decide) v
theorem root5Node34Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root5Node34Domains0 root5Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node34Domains0 root5Node34Domains1
    root5Node34Domains0Fast root5Node34Domains1Fast
    root5Node34Domains0_fast_eq root5Node34Domains1_fast_eq (by decide)
theorem root5Node34Step1_checked :
    checkReplacement table46 root5Node34Domains0 root5Node34Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node34Step1Chunk0_0_checked, root5Node34Step1Chunk0_1_checked, root5Node34Step1Chunk0_2_checked, root5Node34Step1Chunk0_3_checked, root5Node34Step1Chunk0_4_checked, root5Node34Step1Chunk0_5_checked, root5Node34Step1Chunk1_0_checked, root5Node34Step1Chunk1_1_checked, root5Node34Step1Chunk1_2_checked, root5Node34Step1Chunk1_3_checked, root5Node34Step1Chunk1_4_checked, root5Node34Step1Chunk1_5_checked, root5Node34Step1Chunk2_0_checked, root5Node34Step1Chunk2_1_checked, root5Node34Step1Chunk2_2_checked, root5Node34Step1Chunk2_3_checked, root5Node34Step1Chunk2_4_checked, root5Node34Step1Chunk2_5_checked, root5Node34Step1Chunk3_0_checked, root5Node34Step1Chunk3_1_checked, root5Node34Step1Chunk3_2_checked, root5Node34Step1Chunk3_3_checked, root5Node34Step1Chunk3_4_checked, root5Node34Step1Chunk3_5_checked, root5Node34Step1Chunk4_0_checked, root5Node34Step1Chunk4_1_checked, root5Node34Step1Chunk4_2_checked, root5Node34Step1Chunk4_3_checked, root5Node34Step1Chunk4_4_checked, root5Node34Step1Chunk4_5_checked, root5Node34Step1Chunk5_0_checked, root5Node34Step1Chunk5_1_checked, root5Node34Step1Chunk5_2_checked, root5Node34Step1Chunk5_3_checked, root5Node34Step1Chunk5_4_checked, root5Node34Step1Chunk5_5_checked, root5Node34Step1Chunk6_0_checked, root5Node34Step1Chunk6_1_checked, root5Node34Step1Chunk6_2_checked, root5Node34Step1Chunk6_3_checked, root5Node34Step1Chunk6_4_checked, root5Node34Step1Chunk6_5_checked, root5Node34Step1Chunk7_0_checked, root5Node34Step1Chunk7_1_checked, root5Node34Step1Chunk7_2_checked, root5Node34Step1Chunk7_3_checked, root5Node34Step1Chunk7_4_checked, root5Node34Step1Chunk7_5_checked, root5Node34Step1Chunk8_0_checked, root5Node34Step1Chunk8_1_checked, root5Node34Step1Chunk8_2_checked, root5Node34Step1Chunk8_3_checked, root5Node34Step1Chunk8_4_checked, root5Node34Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root5Node34Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node34Domains1 (.output 15) = true := by decide
def root5Node35Domains0 : Domains 61 State := restrict root5Node33Domains1 52 (8,5)
def root5Node35Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(3,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,4)]
  | 16 => some [(1,3)]
  | 17 => some [(5,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(6,5)]
  | 24 => some [(0,4)]
  | 25 => some [(5,4)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(7,5)]
  | 35 => some [(5,4)]
  | 36 => some [(6,4)]
  | 37 => some [(1,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(7,5)]
  | 44 => some [(0,3)]
  | 45 => some [(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(4,2)]
  | 51 => some [(5,3)]
  | 52 => some [(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4)]
  | 57 => some [(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root5Node35Domains0_fast_eq : root5Node35Domains0 = expandDomains root5Node35Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node35Domains0 v = expandDomains root5Node35Domains0Fast v from by decide) v
def root5Node35Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(5,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(3,5)]
  | 9 => [(0,3)]
  | 10 => [(4,1)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(2,4)]
  | 16 => [(1,3)]
  | 17 => [(5,2)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(6,5)]
  | 24 => [(0,4)]
  | 25 => [(5,4)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(4,3)]
  | 34 => [(7,5)]
  | 35 => [(5,4)]
  | 36 => [(6,4)]
  | 37 => [(1,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(1,3)]
  | 43 => [(7,5)]
  | 44 => [(0,3)]
  | 45 => [(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(8,1)]
  | 49 => [(6,5)]
  | 50 => [(4,2)]
  | 51 => [(5,3)]
  | 52 => [(8,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(8,5)]
  | 56 => [(3,4)]
  | 57 => [(6,3)]
  | 58 => [(7,2)]
  | 59 => [(7,4)]
  | _ => [(6,3)]
def root5Node35Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(3,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,4)]
  | 16 => some [(1,3)]
  | 17 => some [(5,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(6,5)]
  | 24 => some [(0,4)]
  | 25 => some [(5,4)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(7,5)]
  | 35 => some [(5,4)]
  | 36 => some [(6,4)]
  | 37 => some [(1,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(7,5)]
  | 44 => some [(0,3)]
  | 45 => some [(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(4,2)]
  | 51 => some [(5,3)]
  | 52 => some [(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => some [(3,4)]
  | 57 => some [(6,3)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root5Node35Domains1_fast_eq : root5Node35Domains1 = expandDomains root5Node35Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node35Domains1 v = expandDomains root5Node35Domains1Fast v from by decide) v
theorem root5Node35Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root5Node35Domains0 root5Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node35Domains0 root5Node35Domains1
    root5Node35Domains0Fast root5Node35Domains1Fast
    root5Node35Domains0_fast_eq root5Node35Domains1_fast_eq (by decide)
theorem root5Node35Step1_checked :
    checkReplacement table46 root5Node35Domains0 root5Node35Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node35Step1Chunk0_0_checked, root5Node35Step1Chunk0_1_checked, root5Node35Step1Chunk0_2_checked, root5Node35Step1Chunk0_3_checked, root5Node35Step1Chunk0_4_checked, root5Node35Step1Chunk0_5_checked, root5Node35Step1Chunk1_0_checked, root5Node35Step1Chunk1_1_checked, root5Node35Step1Chunk1_2_checked, root5Node35Step1Chunk1_3_checked, root5Node35Step1Chunk1_4_checked, root5Node35Step1Chunk1_5_checked, root5Node35Step1Chunk2_0_checked, root5Node35Step1Chunk2_1_checked, root5Node35Step1Chunk2_2_checked, root5Node35Step1Chunk2_3_checked, root5Node35Step1Chunk2_4_checked, root5Node35Step1Chunk2_5_checked, root5Node35Step1Chunk3_0_checked, root5Node35Step1Chunk3_1_checked, root5Node35Step1Chunk3_2_checked, root5Node35Step1Chunk3_3_checked, root5Node35Step1Chunk3_4_checked, root5Node35Step1Chunk3_5_checked, root5Node35Step1Chunk4_0_checked, root5Node35Step1Chunk4_1_checked, root5Node35Step1Chunk4_2_checked, root5Node35Step1Chunk4_3_checked, root5Node35Step1Chunk4_4_checked, root5Node35Step1Chunk4_5_checked, root5Node35Step1Chunk5_0_checked, root5Node35Step1Chunk5_1_checked, root5Node35Step1Chunk5_2_checked, root5Node35Step1Chunk5_3_checked, root5Node35Step1Chunk5_4_checked, root5Node35Step1Chunk5_5_checked, root5Node35Step1Chunk6_0_checked, root5Node35Step1Chunk6_1_checked, root5Node35Step1Chunk6_2_checked, root5Node35Step1Chunk6_3_checked, root5Node35Step1Chunk6_4_checked, root5Node35Step1Chunk6_5_checked, root5Node35Step1Chunk7_0_checked, root5Node35Step1Chunk7_1_checked, root5Node35Step1Chunk7_2_checked, root5Node35Step1Chunk7_3_checked, root5Node35Step1Chunk7_4_checked, root5Node35Step1Chunk7_5_checked, root5Node35Step1Chunk8_0_checked, root5Node35Step1Chunk8_1_checked, root5Node35Step1Chunk8_2_checked, root5Node35Step1Chunk8_3_checked, root5Node35Step1Chunk8_4_checked, root5Node35Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root5Node35Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node35Domains1 (.output 16) = true := by decide
end SpectreFinite.HexSearch.RadiusFour
