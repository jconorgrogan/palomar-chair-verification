module

public import SpectreFinite.RadiusFourRoot7Part2
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable35
public import SpectreFinite.RadiusFourTable37
public import SpectreFinite.RadiusFourTable39
public import SpectreFinite.RadiusFourTable40
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node4Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(4,1)]
  | 1 => [(0,2)]
  | 2 => [(1,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(7,3)]
  | 6 => [(5,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,0)]
  | 17 => [(7,3)]
  | 18 => [(8,5)]
  | 19 => [(1,0)]
  | 20 => [(7,1)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(1,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(8,5)]
  | 33 => [(1,0)]
  | 34 => [(7,1)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(6,3)]
  | 41 => [(7,2)]
  | 42 => [(4,0)]
  | 43 => [(4,3)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(4,1)]
  | 47 => [(0,2)]
  | 48 => [(1,1)]
  | 49 => [(5,1)]
  | 50 => [(0,5)]
  | 51 => [(2,0)]
  | 52 => [(7,3)]
  | 53 => [(5,2)]
  | 54 => [(8,0)]
  | 55 => [(8,3)]
  | 56 => [(3,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(8,4)]
  | _ => [(1,4)]
def root7Node4Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,1)]
  | 1 => some [(0,2)]
  | 2 => some [(1,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,3)]
  | 6 => some [(5,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(8,5)]
  | 19 => some [(1,0)]
  | 20 => some [(7,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(1,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(4,3)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(4,1)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(5,1)]
  | 50 => some [(0,5)]
  | 51 => some [(2,0)]
  | 52 => some [(7,3)]
  | 53 => some [(5,2)]
  | 54 => some [(8,0)]
  | 55 => some [(8,3)]
  | 56 => some [(3,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(1,4)]
theorem root7Node4Domains2_fast_eq : root7Node4Domains2 = expandDomains root7Node4Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node4Domains2 v = expandDomains root7Node4Domains2Fast v from by decide) v
theorem root7Node4Step2Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root7Node4Domains1 root7Node4Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node4Domains1 root7Node4Domains2
    root7Node4Domains1Fast root7Node4Domains2Fast
    root7Node4Domains1_fast_eq root7Node4Domains2_fast_eq (by decide)
theorem root7Node4Step2_checked :
    checkReplacement table40 root7Node4Domains1 root7Node4Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node4Step2Chunk0_0_checked, root7Node4Step2Chunk0_1_checked, root7Node4Step2Chunk0_2_checked, root7Node4Step2Chunk0_3_checked, root7Node4Step2Chunk0_4_checked, root7Node4Step2Chunk0_5_checked, root7Node4Step2Chunk1_0_checked, root7Node4Step2Chunk1_1_checked, root7Node4Step2Chunk1_2_checked, root7Node4Step2Chunk1_3_checked, root7Node4Step2Chunk1_4_checked, root7Node4Step2Chunk1_5_checked, root7Node4Step2Chunk2_0_checked, root7Node4Step2Chunk2_1_checked, root7Node4Step2Chunk2_2_checked, root7Node4Step2Chunk2_3_checked, root7Node4Step2Chunk2_4_checked, root7Node4Step2Chunk2_5_checked, root7Node4Step2Chunk3_0_checked, root7Node4Step2Chunk3_1_checked, root7Node4Step2Chunk3_2_checked, root7Node4Step2Chunk3_3_checked, root7Node4Step2Chunk3_4_checked, root7Node4Step2Chunk3_5_checked, root7Node4Step2Chunk4_0_checked, root7Node4Step2Chunk4_1_checked, root7Node4Step2Chunk4_2_checked, root7Node4Step2Chunk4_3_checked, root7Node4Step2Chunk4_4_checked, root7Node4Step2Chunk4_5_checked, root7Node4Step2Chunk5_0_checked, root7Node4Step2Chunk5_1_checked, root7Node4Step2Chunk5_2_checked, root7Node4Step2Chunk5_3_checked, root7Node4Step2Chunk5_4_checked, root7Node4Step2Chunk5_5_checked, root7Node4Step2Chunk6_0_checked, root7Node4Step2Chunk6_1_checked, root7Node4Step2Chunk6_2_checked, root7Node4Step2Chunk6_3_checked, root7Node4Step2Chunk6_4_checked, root7Node4Step2Chunk6_5_checked, root7Node4Step2Chunk7_0_checked, root7Node4Step2Chunk7_1_checked, root7Node4Step2Chunk7_2_checked, root7Node4Step2Chunk7_3_checked, root7Node4Step2Chunk7_4_checked, root7Node4Step2Chunk7_5_checked, root7Node4Step2Chunk8_0_checked, root7Node4Step2Chunk8_1_checked, root7Node4Step2Chunk8_2_checked, root7Node4Step2Chunk8_3_checked, root7Node4Step2Chunk8_4_checked, root7Node4Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root7Node4Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node4Domains2 (.output 0) = true := by decide
def root7Node5Domains0 : Domains 61 State := restrict root7Node3Domains2 11 (6,4)
def root7Node5Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,1)]
  | 1 => some [(0,2)]
  | 2 => some [(1,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,3)]
  | 6 => some [(5,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2),(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5),(8,5)]
  | 19 => some [(0,3),(1,0)]
  | 20 => some [(7,1),(8,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(1,3),(7,3)]
  | 27 => some [(4,2),(8,2)]
  | 28 => some [(5,0),(5,3)]
  | 29 => some [(4,5),(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5),(8,5)]
  | 33 => some [(1,0)]
  | 34 => some [(2,1),(7,1)]
  | 35 => some [(0,4),(1,2),(6,2)]
  | 36 => some [(1,4),(3,4),(5,4),(7,4)]
  | 37 => some [(0,0),(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(7,4)]
  | 40 => some [(0,5),(1,3),(6,3)]
  | 41 => some [(4,4),(7,2),(8,2)]
  | 42 => some [(0,0),(4,0),(5,0),(8,0)]
  | 43 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 44 => some [(0,2),(1,5),(6,0)]
  | 45 => some [(1,1),(6,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(7,1)]
  | 49 => some [(1,5),(5,1),(5,4)]
  | 50 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 51 => some [(2,0),(4,0),(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(5,2),(5,5),(8,2)]
  | 54 => some [(5,0),(7,0),(8,0)]
  | 55 => some [(4,3),(4,5),(8,3)]
  | 56 => some [(3,1),(5,1),(5,4),(8,4)]
  | 57 => some [(0,1),(1,4)]
  | 58 => some [(0,5),(6,2)]
  | 59 => some [(4,4),(8,4)]
  | _ => some [(0,0),(1,4)]
theorem root7Node5Domains0_fast_eq : root7Node5Domains0 = expandDomains root7Node5Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node5Domains0 v = expandDomains root7Node5Domains0Fast v from by decide) v
def root7Node5Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(4,1)]
  | 1 => [(0,2)]
  | 2 => [(1,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(7,3)]
  | 6 => [(5,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,0)]
  | 17 => [(7,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(8,1)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(1,3),(7,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(5,5),(8,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(5,5),(8,5)]
  | 33 => [(1,0)]
  | 34 => [(2,1),(7,1)]
  | 35 => [(0,4),(1,2),(6,2)]
  | 36 => [(1,4),(3,4),(7,4)]
  | 37 => [(0,5),(6,3)]
  | 38 => [(4,4),(7,2)]
  | 39 => [(1,4),(7,4)]
  | 40 => [(0,5),(1,3),(6,3)]
  | 41 => [(4,4),(7,2),(8,2)]
  | 42 => [(0,0),(4,0),(5,0),(8,0)]
  | 43 => [(2,1),(2,3),(2,5),(4,1)]
  | 44 => [(0,2),(6,0)]
  | 45 => [(1,1),(7,1)]
  | 46 => [(4,1),(7,5),(8,1)]
  | 47 => [(0,2),(6,0),(6,5)]
  | 48 => [(0,4),(1,1),(7,1)]
  | 49 => [(1,5),(5,1),(5,4)]
  | 50 => [(1,2),(3,2),(5,2),(7,2)]
  | 51 => [(4,0),(8,0)]
  | 52 => [(7,3),(8,3)]
  | 53 => [(5,2),(5,5),(8,2)]
  | 54 => [(5,0),(7,0),(8,0)]
  | 55 => [(4,3),(4,5),(8,3)]
  | 56 => [(5,1),(5,4),(8,4)]
  | 57 => [(0,1),(1,4)]
  | 58 => [(0,5),(6,2)]
  | 59 => [(4,4),(8,4)]
  | _ => [(0,0),(1,4)]
def root7Node5Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,1)]
  | 1 => some [(0,2)]
  | 2 => some [(1,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,3)]
  | 6 => some [(5,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(1,3),(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5),(8,5)]
  | 33 => some [(1,0)]
  | 34 => some [(2,1),(7,1)]
  | 35 => some [(0,4),(1,2),(6,2)]
  | 36 => some [(1,4),(3,4),(7,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(7,4)]
  | 40 => some [(0,5),(1,3),(6,3)]
  | 41 => some [(4,4),(7,2),(8,2)]
  | 42 => some [(0,0),(4,0),(5,0),(8,0)]
  | 43 => some [(2,1),(2,3),(2,5),(4,1)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(7,1)]
  | 49 => some [(1,5),(5,1),(5,4)]
  | 50 => some [(1,2),(3,2),(5,2),(7,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(5,2),(5,5),(8,2)]
  | 54 => some [(5,0),(7,0),(8,0)]
  | 55 => some [(4,3),(4,5),(8,3)]
  | 56 => some [(5,1),(5,4),(8,4)]
  | 57 => some [(0,1),(1,4)]
  | 58 => some [(0,5),(6,2)]
  | 59 => some [(4,4),(8,4)]
  | _ => some [(0,0),(1,4)]
theorem root7Node5Domains1_fast_eq : root7Node5Domains1 = expandDomains root7Node5Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node5Domains1 v = expandDomains root7Node5Domains1Fast v from by decide) v
theorem root7Node5Step1Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root7Node5Domains0 root7Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node5Domains0 root7Node5Domains1
    root7Node5Domains0Fast root7Node5Domains1Fast
    root7Node5Domains0_fast_eq root7Node5Domains1_fast_eq (by decide)
theorem root7Node5Step1_checked :
    checkReplacement table35 root7Node5Domains0 root7Node5Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node5Step1Chunk0_0_checked, root7Node5Step1Chunk0_1_checked, root7Node5Step1Chunk0_2_checked, root7Node5Step1Chunk0_3_checked, root7Node5Step1Chunk0_4_checked, root7Node5Step1Chunk0_5_checked, root7Node5Step1Chunk1_0_checked, root7Node5Step1Chunk1_1_checked, root7Node5Step1Chunk1_2_checked, root7Node5Step1Chunk1_3_checked, root7Node5Step1Chunk1_4_checked, root7Node5Step1Chunk1_5_checked, root7Node5Step1Chunk2_0_checked, root7Node5Step1Chunk2_1_checked, root7Node5Step1Chunk2_2_checked, root7Node5Step1Chunk2_3_checked, root7Node5Step1Chunk2_4_checked, root7Node5Step1Chunk2_5_checked, root7Node5Step1Chunk3_0_checked, root7Node5Step1Chunk3_1_checked, root7Node5Step1Chunk3_2_checked, root7Node5Step1Chunk3_3_checked, root7Node5Step1Chunk3_4_checked, root7Node5Step1Chunk3_5_checked, root7Node5Step1Chunk4_0_checked, root7Node5Step1Chunk4_1_checked, root7Node5Step1Chunk4_2_checked, root7Node5Step1Chunk4_3_checked, root7Node5Step1Chunk4_4_checked, root7Node5Step1Chunk4_5_checked, root7Node5Step1Chunk5_0_checked, root7Node5Step1Chunk5_1_checked, root7Node5Step1Chunk5_2_checked, root7Node5Step1Chunk5_3_checked, root7Node5Step1Chunk5_4_checked, root7Node5Step1Chunk5_5_checked, root7Node5Step1Chunk6_0_checked, root7Node5Step1Chunk6_1_checked, root7Node5Step1Chunk6_2_checked, root7Node5Step1Chunk6_3_checked, root7Node5Step1Chunk6_4_checked, root7Node5Step1Chunk6_5_checked, root7Node5Step1Chunk7_0_checked, root7Node5Step1Chunk7_1_checked, root7Node5Step1Chunk7_2_checked, root7Node5Step1Chunk7_3_checked, root7Node5Step1Chunk7_4_checked, root7Node5Step1Chunk7_5_checked, root7Node5Step1Chunk8_0_checked, root7Node5Step1Chunk8_1_checked, root7Node5Step1Chunk8_2_checked, root7Node5Step1Chunk8_3_checked, root7Node5Step1Chunk8_4_checked, root7Node5Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node6Domains0 : Domains 61 State := restrict root7Node5Domains1 26 (1,3)
def root7Node6Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,1)]
  | 1 => some [(0,2)]
  | 2 => some [(1,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,3)]
  | 6 => some [(5,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(1,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5),(8,5)]
  | 33 => some [(1,0)]
  | 34 => some [(2,1),(7,1)]
  | 35 => some [(0,4),(1,2),(6,2)]
  | 36 => some [(1,4),(3,4),(7,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(7,4)]
  | 40 => some [(0,5),(1,3),(6,3)]
  | 41 => some [(4,4),(7,2),(8,2)]
  | 42 => some [(0,0),(4,0),(5,0),(8,0)]
  | 43 => some [(2,1),(2,3),(2,5),(4,1)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(7,1)]
  | 49 => some [(1,5),(5,1),(5,4)]
  | 50 => some [(1,2),(3,2),(5,2),(7,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(5,2),(5,5),(8,2)]
  | 54 => some [(5,0),(7,0),(8,0)]
  | 55 => some [(4,3),(4,5),(8,3)]
  | 56 => some [(5,1),(5,4),(8,4)]
  | 57 => some [(0,1),(1,4)]
  | 58 => some [(0,5),(6,2)]
  | 59 => some [(4,4),(8,4)]
  | _ => some [(0,0),(1,4)]
theorem root7Node6Domains0_fast_eq : root7Node6Domains0 = expandDomains root7Node6Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node6Domains0 v = expandDomains root7Node6Domains0Fast v from by decide) v
def root7Node6Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(4,1)]
  | 1 => [(0,2)]
  | 2 => [(1,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(7,3)]
  | 6 => [(5,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,0)]
  | 17 => [(7,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(8,1)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(1,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(5,5),(8,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(5,5),(8,5)]
  | 33 => [(1,0)]
  | 34 => [(2,1),(7,1)]
  | 35 => [(0,4)]
  | 36 => [(1,4),(3,4)]
  | 37 => [(0,5),(6,3)]
  | 38 => [(4,4),(7,2)]
  | 39 => [(1,4),(7,4)]
  | 40 => [(0,5),(6,3)]
  | 41 => [(4,4),(7,2),(8,2)]
  | 42 => [(0,0),(4,0),(5,0),(8,0)]
  | 43 => [(2,3),(2,5)]
  | 44 => [(0,2),(6,0)]
  | 45 => [(1,1),(7,1)]
  | 46 => [(4,1),(7,5)]
  | 47 => [(0,2),(6,0)]
  | 48 => [(0,4),(1,1),(7,1)]
  | 49 => [(1,5),(5,1),(5,4)]
  | 50 => [(1,2),(7,2)]
  | 51 => [(4,0)]
  | 52 => [(7,3)]
  | 53 => [(5,2),(8,2)]
  | 54 => [(5,0),(7,0),(8,0)]
  | 55 => [(4,3),(4,5),(8,3)]
  | 56 => [(5,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(4,4),(8,4)]
  | _ => [(0,0),(1,4)]
def root7Node6Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,1)]
  | 1 => some [(0,2)]
  | 2 => some [(1,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,3)]
  | 6 => some [(5,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(1,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5),(8,5)]
  | 33 => some [(1,0)]
  | 34 => some [(2,1),(7,1)]
  | 35 => some [(0,4)]
  | 36 => some [(1,4),(3,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(7,4)]
  | 40 => some [(0,5),(6,3)]
  | 41 => some [(4,4),(7,2),(8,2)]
  | 42 => some [(0,0),(4,0),(5,0),(8,0)]
  | 43 => some [(2,3),(2,5)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(4,1),(7,5)]
  | 47 => some [(0,2),(6,0)]
  | 48 => some [(0,4),(1,1),(7,1)]
  | 49 => some [(1,5),(5,1),(5,4)]
  | 50 => some [(1,2),(7,2)]
  | 51 => some [(4,0)]
  | 52 => some [(7,3)]
  | 53 => some [(5,2),(8,2)]
  | 54 => some [(5,0),(7,0),(8,0)]
  | 55 => some [(4,3),(4,5),(8,3)]
  | 56 => some [(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(4,4),(8,4)]
  | _ => some [(0,0),(1,4)]
theorem root7Node6Domains1_fast_eq : root7Node6Domains1 = expandDomains root7Node6Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node6Domains1 v = expandDomains root7Node6Domains1Fast v from by decide) v
theorem root7Node6Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root7Node6Domains0 root7Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains0 root7Node6Domains1
    root7Node6Domains0Fast root7Node6Domains1Fast
    root7Node6Domains0_fast_eq root7Node6Domains1_fast_eq (by decide)
theorem root7Node6Step1_checked :
    checkReplacement table37 root7Node6Domains0 root7Node6Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node6Step1Chunk0_0_checked, root7Node6Step1Chunk0_1_checked, root7Node6Step1Chunk0_2_checked, root7Node6Step1Chunk0_3_checked, root7Node6Step1Chunk0_4_checked, root7Node6Step1Chunk0_5_checked, root7Node6Step1Chunk1_0_checked, root7Node6Step1Chunk1_1_checked, root7Node6Step1Chunk1_2_checked, root7Node6Step1Chunk1_3_checked, root7Node6Step1Chunk1_4_checked, root7Node6Step1Chunk1_5_checked, root7Node6Step1Chunk2_0_checked, root7Node6Step1Chunk2_1_checked, root7Node6Step1Chunk2_2_checked, root7Node6Step1Chunk2_3_checked, root7Node6Step1Chunk2_4_checked, root7Node6Step1Chunk2_5_checked, root7Node6Step1Chunk3_0_checked, root7Node6Step1Chunk3_1_checked, root7Node6Step1Chunk3_2_checked, root7Node6Step1Chunk3_3_checked, root7Node6Step1Chunk3_4_checked, root7Node6Step1Chunk3_5_checked, root7Node6Step1Chunk4_0_checked, root7Node6Step1Chunk4_1_checked, root7Node6Step1Chunk4_2_checked, root7Node6Step1Chunk4_3_checked, root7Node6Step1Chunk4_4_checked, root7Node6Step1Chunk4_5_checked, root7Node6Step1Chunk5_0_checked, root7Node6Step1Chunk5_1_checked, root7Node6Step1Chunk5_2_checked, root7Node6Step1Chunk5_3_checked, root7Node6Step1Chunk5_4_checked, root7Node6Step1Chunk5_5_checked, root7Node6Step1Chunk6_0_checked, root7Node6Step1Chunk6_1_checked, root7Node6Step1Chunk6_2_checked, root7Node6Step1Chunk6_3_checked, root7Node6Step1Chunk6_4_checked, root7Node6Step1Chunk6_5_checked, root7Node6Step1Chunk7_0_checked, root7Node6Step1Chunk7_1_checked, root7Node6Step1Chunk7_2_checked, root7Node6Step1Chunk7_3_checked, root7Node6Step1Chunk7_4_checked, root7Node6Step1Chunk7_5_checked, root7Node6Step1Chunk8_0_checked, root7Node6Step1Chunk8_1_checked, root7Node6Step1Chunk8_2_checked, root7Node6Step1Chunk8_3_checked, root7Node6Step1Chunk8_4_checked, root7Node6Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node6Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(4,1)]
  | 1 => [(0,2)]
  | 2 => [(1,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(7,3)]
  | 6 => [(5,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,0)]
  | 17 => [(7,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(8,1)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(1,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(5,5),(8,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(5,5),(8,5)]
  | 33 => [(1,0)]
  | 34 => [(2,1),(7,1)]
  | 35 => [(0,4)]
  | 36 => [(1,4),(3,4)]
  | 37 => [(0,5),(6,3)]
  | 38 => [(4,4),(7,2)]
  | 39 => [(1,4),(7,4)]
  | 40 => [(0,5),(6,3)]
  | 41 => [(4,4),(7,2)]
  | 42 => [(0,0),(4,0)]
  | 43 => [(2,3),(2,5)]
  | 44 => [(0,2),(6,0)]
  | 45 => [(1,1),(7,1)]
  | 46 => [(4,1),(7,5)]
  | 47 => [(0,2),(6,0)]
  | 48 => [(1,1),(7,1)]
  | 49 => [(1,5),(5,1)]
  | 50 => [(1,2),(7,2)]
  | 51 => [(4,0)]
  | 52 => [(7,3)]
  | 53 => [(5,2),(8,2)]
  | 54 => [(5,0),(8,0)]
  | 55 => [(4,5),(8,3)]
  | 56 => [(5,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(8,4)]
  | _ => [(0,0),(1,4)]
def root7Node6Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,1)]
  | 1 => some [(0,2)]
  | 2 => some [(1,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,3)]
  | 6 => some [(5,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(1,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5),(8,5)]
  | 33 => some [(1,0)]
  | 34 => some [(2,1),(7,1)]
  | 35 => some [(0,4)]
  | 36 => some [(1,4),(3,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(7,4)]
  | 40 => some [(0,5),(6,3)]
  | 41 => some [(4,4),(7,2)]
  | 42 => some [(0,0),(4,0)]
  | 43 => some [(2,3),(2,5)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(4,1),(7,5)]
  | 47 => some [(0,2),(6,0)]
  | 48 => some [(1,1),(7,1)]
  | 49 => some [(1,5),(5,1)]
  | 50 => some [(1,2),(7,2)]
  | 51 => some [(4,0)]
  | 52 => some [(7,3)]
  | 53 => some [(5,2),(8,2)]
  | 54 => some [(5,0),(8,0)]
  | 55 => some [(4,5),(8,3)]
  | 56 => some [(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(0,0),(1,4)]
theorem root7Node6Domains2_fast_eq : root7Node6Domains2 = expandDomains root7Node6Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node6Domains2 v = expandDomains root7Node6Domains2Fast v from by decide) v
theorem root7Node6Step2Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root7Node6Domains1 root7Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node6Domains1 root7Node6Domains2
    root7Node6Domains1Fast root7Node6Domains2Fast
    root7Node6Domains1_fast_eq root7Node6Domains2_fast_eq (by decide)
theorem root7Node6Step2_checked :
    checkReplacement table39 root7Node6Domains1 root7Node6Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node6Step2Chunk0_0_checked, root7Node6Step2Chunk0_1_checked, root7Node6Step2Chunk0_2_checked, root7Node6Step2Chunk0_3_checked, root7Node6Step2Chunk0_4_checked, root7Node6Step2Chunk0_5_checked, root7Node6Step2Chunk1_0_checked, root7Node6Step2Chunk1_1_checked, root7Node6Step2Chunk1_2_checked, root7Node6Step2Chunk1_3_checked, root7Node6Step2Chunk1_4_checked, root7Node6Step2Chunk1_5_checked, root7Node6Step2Chunk2_0_checked, root7Node6Step2Chunk2_1_checked, root7Node6Step2Chunk2_2_checked, root7Node6Step2Chunk2_3_checked, root7Node6Step2Chunk2_4_checked, root7Node6Step2Chunk2_5_checked, root7Node6Step2Chunk3_0_checked, root7Node6Step2Chunk3_1_checked, root7Node6Step2Chunk3_2_checked, root7Node6Step2Chunk3_3_checked, root7Node6Step2Chunk3_4_checked, root7Node6Step2Chunk3_5_checked, root7Node6Step2Chunk4_0_checked, root7Node6Step2Chunk4_1_checked, root7Node6Step2Chunk4_2_checked, root7Node6Step2Chunk4_3_checked, root7Node6Step2Chunk4_4_checked, root7Node6Step2Chunk4_5_checked, root7Node6Step2Chunk5_0_checked, root7Node6Step2Chunk5_1_checked, root7Node6Step2Chunk5_2_checked, root7Node6Step2Chunk5_3_checked, root7Node6Step2Chunk5_4_checked, root7Node6Step2Chunk5_5_checked, root7Node6Step2Chunk6_0_checked, root7Node6Step2Chunk6_1_checked, root7Node6Step2Chunk6_2_checked, root7Node6Step2Chunk6_3_checked, root7Node6Step2Chunk6_4_checked, root7Node6Step2Chunk6_5_checked, root7Node6Step2Chunk7_0_checked, root7Node6Step2Chunk7_1_checked, root7Node6Step2Chunk7_2_checked, root7Node6Step2Chunk7_3_checked, root7Node6Step2Chunk7_4_checked, root7Node6Step2Chunk7_5_checked, root7Node6Step2Chunk8_0_checked, root7Node6Step2Chunk8_1_checked, root7Node6Step2Chunk8_2_checked, root7Node6Step2Chunk8_3_checked, root7Node6Step2Chunk8_4_checked, root7Node6Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node7Domains0 : Domains 61 State := restrict root7Node6Domains2 29 (5,5)
def root7Node7Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,1)]
  | 1 => some [(0,2)]
  | 2 => some [(1,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,3)]
  | 6 => some [(5,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(1,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5),(8,5)]
  | 33 => some [(1,0)]
  | 34 => some [(2,1),(7,1)]
  | 35 => some [(0,4)]
  | 36 => some [(1,4),(3,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(7,4)]
  | 40 => some [(0,5),(6,3)]
  | 41 => some [(4,4),(7,2)]
  | 42 => some [(0,0),(4,0)]
  | 43 => some [(2,3),(2,5)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(4,1),(7,5)]
  | 47 => some [(0,2),(6,0)]
  | 48 => some [(1,1),(7,1)]
  | 49 => some [(1,5),(5,1)]
  | 50 => some [(1,2),(7,2)]
  | 51 => some [(4,0)]
  | 52 => some [(7,3)]
  | 53 => some [(5,2),(8,2)]
  | 54 => some [(5,0),(8,0)]
  | 55 => some [(4,5),(8,3)]
  | 56 => some [(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(0,0),(1,4)]
theorem root7Node7Domains0_fast_eq : root7Node7Domains0 = expandDomains root7Node7Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node7Domains0 v = expandDomains root7Node7Domains0Fast v from by decide) v
def root7Node7Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(4,1)]
  | 1 => [(0,2)]
  | 2 => [(1,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(7,3)]
  | 6 => [(5,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,0)]
  | 17 => [(7,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(8,1)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(1,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(5,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(5,5)]
  | 33 => [(1,0)]
  | 34 => [(2,1),(7,1)]
  | 35 => [(0,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(1,4)]
  | 40 => [(0,5)]
  | 41 => [(4,4)]
  | 42 => [(0,0),(4,0)]
  | 43 => [(2,5)]
  | 44 => [(6,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(6,0)]
  | 48 => [(7,1)]
  | 49 => [(1,5)]
  | 50 => [(7,2)]
  | 51 => [(4,0)]
  | 52 => [(7,3)]
  | 53 => [(8,2)]
  | 54 => [(5,0)]
  | 55 => [(4,5)]
  | 56 => [(5,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(8,4)]
  | _ => [(0,0)]
def root7Node7Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,1)]
  | 1 => some [(0,2)]
  | 2 => some [(1,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,3)]
  | 6 => some [(5,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(1,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5)]
  | 33 => some [(1,0)]
  | 34 => some [(2,1),(7,1)]
  | 35 => some [(0,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(4,4)]
  | 42 => some [(0,0),(4,0)]
  | 43 => some [(2,5)]
  | 44 => some [(6,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(1,5)]
  | 50 => some [(7,2)]
  | 51 => some [(4,0)]
  | 52 => some [(7,3)]
  | 53 => some [(8,2)]
  | 54 => some [(5,0)]
  | 55 => some [(4,5)]
  | 56 => some [(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(0,0)]
theorem root7Node7Domains1_fast_eq : root7Node7Domains1 = expandDomains root7Node7Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node7Domains1 v = expandDomains root7Node7Domains1Fast v from by decide) v
theorem root7Node7Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root7Node7Domains0 root7Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node7Domains0 root7Node7Domains1
    root7Node7Domains0Fast root7Node7Domains1Fast
    root7Node7Domains0_fast_eq root7Node7Domains1_fast_eq (by decide)
theorem root7Node7Step1_checked :
    checkReplacement table46 root7Node7Domains0 root7Node7Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node7Step1Chunk0_0_checked, root7Node7Step1Chunk0_1_checked, root7Node7Step1Chunk0_2_checked, root7Node7Step1Chunk0_3_checked, root7Node7Step1Chunk0_4_checked, root7Node7Step1Chunk0_5_checked, root7Node7Step1Chunk1_0_checked, root7Node7Step1Chunk1_1_checked, root7Node7Step1Chunk1_2_checked, root7Node7Step1Chunk1_3_checked, root7Node7Step1Chunk1_4_checked, root7Node7Step1Chunk1_5_checked, root7Node7Step1Chunk2_0_checked, root7Node7Step1Chunk2_1_checked, root7Node7Step1Chunk2_2_checked, root7Node7Step1Chunk2_3_checked, root7Node7Step1Chunk2_4_checked, root7Node7Step1Chunk2_5_checked, root7Node7Step1Chunk3_0_checked, root7Node7Step1Chunk3_1_checked, root7Node7Step1Chunk3_2_checked, root7Node7Step1Chunk3_3_checked, root7Node7Step1Chunk3_4_checked, root7Node7Step1Chunk3_5_checked, root7Node7Step1Chunk4_0_checked, root7Node7Step1Chunk4_1_checked, root7Node7Step1Chunk4_2_checked, root7Node7Step1Chunk4_3_checked, root7Node7Step1Chunk4_4_checked, root7Node7Step1Chunk4_5_checked, root7Node7Step1Chunk5_0_checked, root7Node7Step1Chunk5_1_checked, root7Node7Step1Chunk5_2_checked, root7Node7Step1Chunk5_3_checked, root7Node7Step1Chunk5_4_checked, root7Node7Step1Chunk5_5_checked, root7Node7Step1Chunk6_0_checked, root7Node7Step1Chunk6_1_checked, root7Node7Step1Chunk6_2_checked, root7Node7Step1Chunk6_3_checked, root7Node7Step1Chunk6_4_checked, root7Node7Step1Chunk6_5_checked, root7Node7Step1Chunk7_0_checked, root7Node7Step1Chunk7_1_checked, root7Node7Step1Chunk7_2_checked, root7Node7Step1Chunk7_3_checked, root7Node7Step1Chunk7_4_checked, root7Node7Step1Chunk7_5_checked, root7Node7Step1Chunk8_0_checked, root7Node7Step1Chunk8_1_checked, root7Node7Step1Chunk8_2_checked, root7Node7Step1Chunk8_3_checked, root7Node7Step1Chunk8_4_checked, root7Node7Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
