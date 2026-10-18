module

public import SpectreFinite.RadiusFourRoot0Part10
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable26
public import SpectreFinite.RadiusFourTable36
public import SpectreFinite.RadiusFourTable40

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node29Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(3,5)]
  | 3 => [(0,3)]
  | 4 => [(4,1)]
  | 5 => [(4,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(2,4)]
  | 9 => [(1,3)]
  | 10 => [(5,2)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(6,0)]
  | 14 => [(7,1)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(7,0)]
  | 24 => [(4,3)]
  | 25 => [(7,5)]
  | 26 => [(5,1)]
  | 27 => [(0,1)]
  | 28 => [(6,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(7,4)]
  | 33 => [(1,3)]
  | 34 => [(8,2)]
  | 35 => [(8,5)]
  | 36 => [(1,0)]
  | 37 => [(7,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(8,1)]
  | 41 => [(6,5)]
  | 42 => [(0,4)]
  | 43 => [(8,2)]
  | 44 => [(5,0)]
  | 45 => [(4,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(8,5)]
  | 49 => [(7,0)]
  | 50 => [(5,4)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(1,5)]
  | 57 => [(6,1)]
  | 58 => [(4,1)]
  | 59 => [(0,2)]
  | _ => [(1,1)]
def root0Node29Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(3,5)]
  | 3 => some [(0,3)]
  | 4 => some [(4,1)]
  | 5 => some [(4,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(2,4)]
  | 9 => some [(1,3)]
  | 10 => some [(5,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(4,3)]
  | 25 => some [(7,5)]
  | 26 => some [(5,1)]
  | 27 => some [(0,1)]
  | 28 => some [(6,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(1,3)]
  | 34 => some [(8,2)]
  | 35 => some [(8,5)]
  | 36 => some [(1,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(8,1)]
  | 41 => some [(6,5)]
  | 42 => some [(0,4)]
  | 43 => some [(8,2)]
  | 44 => some [(5,0)]
  | 45 => some [(4,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(7,0)]
  | 50 => some [(5,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(1,5)]
  | 57 => some [(6,1)]
  | 58 => some [(4,1)]
  | 59 => some [(0,2)]
  | _ => some [(1,1)]
theorem root0Node29Domains2_fast_eq : root0Node29Domains2 = expandDomains root0Node29Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node29Domains2 v = expandDomains root0Node29Domains2Fast v from by decide) v
theorem root0Node29Step2Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root0Node29Domains1 root0Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node29Domains1 root0Node29Domains2
    root0Node29Domains1Fast root0Node29Domains2Fast
    root0Node29Domains1_fast_eq root0Node29Domains2_fast_eq (by decide)
theorem root0Node29Step2_checked :
    checkReplacement table40 root0Node29Domains1 root0Node29Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node29Step2Chunk0_0_checked, root0Node29Step2Chunk0_1_checked, root0Node29Step2Chunk0_2_checked, root0Node29Step2Chunk0_3_checked, root0Node29Step2Chunk0_4_checked, root0Node29Step2Chunk0_5_checked, root0Node29Step2Chunk1_0_checked, root0Node29Step2Chunk1_1_checked, root0Node29Step2Chunk1_2_checked, root0Node29Step2Chunk1_3_checked, root0Node29Step2Chunk1_4_checked, root0Node29Step2Chunk1_5_checked, root0Node29Step2Chunk2_0_checked, root0Node29Step2Chunk2_1_checked, root0Node29Step2Chunk2_2_checked, root0Node29Step2Chunk2_3_checked, root0Node29Step2Chunk2_4_checked, root0Node29Step2Chunk2_5_checked, root0Node29Step2Chunk3_0_checked, root0Node29Step2Chunk3_1_checked, root0Node29Step2Chunk3_2_checked, root0Node29Step2Chunk3_3_checked, root0Node29Step2Chunk3_4_checked, root0Node29Step2Chunk3_5_checked, root0Node29Step2Chunk4_0_checked, root0Node29Step2Chunk4_1_checked, root0Node29Step2Chunk4_2_checked, root0Node29Step2Chunk4_3_checked, root0Node29Step2Chunk4_4_checked, root0Node29Step2Chunk4_5_checked, root0Node29Step2Chunk5_0_checked, root0Node29Step2Chunk5_1_checked, root0Node29Step2Chunk5_2_checked, root0Node29Step2Chunk5_3_checked, root0Node29Step2Chunk5_4_checked, root0Node29Step2Chunk5_5_checked, root0Node29Step2Chunk6_0_checked, root0Node29Step2Chunk6_1_checked, root0Node29Step2Chunk6_2_checked, root0Node29Step2Chunk6_3_checked, root0Node29Step2Chunk6_4_checked, root0Node29Step2Chunk6_5_checked, root0Node29Step2Chunk7_0_checked, root0Node29Step2Chunk7_1_checked, root0Node29Step2Chunk7_2_checked, root0Node29Step2Chunk7_3_checked, root0Node29Step2Chunk7_4_checked, root0Node29Step2Chunk7_5_checked, root0Node29Step2Chunk8_0_checked, root0Node29Step2Chunk8_1_checked, root0Node29Step2Chunk8_2_checked, root0Node29Step2Chunk8_3_checked, root0Node29Step2Chunk8_4_checked, root0Node29Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root0Node29Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node29Domains2 (.output 12) = true := by decide
def root0Node30Domains0 : Domains 61 State := restrict root0Node28Domains2 18 (8,0)
def root0Node30Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(3,5)]
  | 3 => some [(0,3)]
  | 4 => some [(4,1)]
  | 5 => some [(4,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(2,4)]
  | 9 => some [(1,3)]
  | 10 => some [(5,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(4,3)]
  | 25 => some [(7,5)]
  | 26 => some [(5,1),(5,4),(8,4)]
  | 27 => some [(0,1),(6,4)]
  | 28 => some [(1,2),(6,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(1,3)]
  | 34 => some [(4,2),(8,2)]
  | 35 => some [(7,5),(8,5)]
  | 36 => some [(0,3),(1,0)]
  | 37 => some [(7,1),(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(8,1)]
  | 41 => some [(6,5)]
  | 42 => some [(0,4)]
  | 43 => some [(4,2),(8,2)]
  | 44 => some [(5,0),(5,3)]
  | 45 => some [(4,5),(5,5),(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(3,0),(7,0)]
  | 50 => some [(1,4),(3,4),(5,4),(7,4)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(0,2),(1,5),(6,0)]
  | 57 => some [(1,1),(6,1),(7,1)]
  | 58 => some [(4,1),(7,5)]
  | 59 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root0Node30Domains0_fast_eq : root0Node30Domains0 = expandDomains root0Node30Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node30Domains0 v = expandDomains root0Node30Domains0Fast v from by decide) v
def root0Node30Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(3,5)]
  | 3 => [(0,3)]
  | 4 => [(4,1)]
  | 5 => [(4,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(2,4)]
  | 9 => [(1,3)]
  | 10 => [(5,2)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(6,0)]
  | 14 => [(7,1)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(7,0)]
  | 24 => [(4,3)]
  | 25 => [(7,5)]
  | 26 => [(5,4),(8,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(7,4)]
  | 33 => [(1,3)]
  | 34 => [(4,2),(8,2)]
  | 35 => [(7,5)]
  | 36 => [(0,3)]
  | 37 => [(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(8,1)]
  | 41 => [(6,5)]
  | 42 => [(0,4)]
  | 43 => [(4,2)]
  | 44 => [(5,3)]
  | 45 => [(5,5),(8,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(5,5),(8,5)]
  | 49 => [(3,0),(7,0)]
  | 50 => [(1,4),(3,4),(7,4)]
  | 51 => [(0,5),(6,3)]
  | 52 => [(4,4),(7,2)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(0,2),(6,0)]
  | 57 => [(1,1),(7,1)]
  | 58 => [(4,1),(7,5)]
  | 59 => [(0,2),(6,0)]
  | _ => [(1,1),(7,1)]
def root0Node30Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(3,5)]
  | 3 => some [(0,3)]
  | 4 => some [(4,1)]
  | 5 => some [(4,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(2,4)]
  | 9 => some [(1,3)]
  | 10 => some [(5,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(4,3)]
  | 25 => some [(7,5)]
  | 26 => some [(5,4),(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(1,3)]
  | 34 => some [(4,2),(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(0,3)]
  | 37 => some [(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(8,1)]
  | 41 => some [(6,5)]
  | 42 => some [(0,4)]
  | 43 => some [(4,2)]
  | 44 => some [(5,3)]
  | 45 => some [(5,5),(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(3,0),(7,0)]
  | 50 => some [(1,4),(3,4),(7,4)]
  | 51 => some [(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(0,2),(6,0)]
  | 57 => some [(1,1),(7,1)]
  | 58 => some [(4,1),(7,5)]
  | 59 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root0Node30Domains1_fast_eq : root0Node30Domains1 = expandDomains root0Node30Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node30Domains1 v = expandDomains root0Node30Domains1Fast v from by decide) v
theorem root0Node30Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root0Node30Domains0 root0Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node30Domains0 root0Node30Domains1
    root0Node30Domains0Fast root0Node30Domains1Fast
    root0Node30Domains0_fast_eq root0Node30Domains1_fast_eq (by decide)
theorem root0Node30Step1_checked :
    checkReplacement table36 root0Node30Domains0 root0Node30Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node30Step1Chunk0_0_checked, root0Node30Step1Chunk0_1_checked, root0Node30Step1Chunk0_2_checked, root0Node30Step1Chunk0_3_checked, root0Node30Step1Chunk0_4_checked, root0Node30Step1Chunk0_5_checked, root0Node30Step1Chunk1_0_checked, root0Node30Step1Chunk1_1_checked, root0Node30Step1Chunk1_2_checked, root0Node30Step1Chunk1_3_checked, root0Node30Step1Chunk1_4_checked, root0Node30Step1Chunk1_5_checked, root0Node30Step1Chunk2_0_checked, root0Node30Step1Chunk2_1_checked, root0Node30Step1Chunk2_2_checked, root0Node30Step1Chunk2_3_checked, root0Node30Step1Chunk2_4_checked, root0Node30Step1Chunk2_5_checked, root0Node30Step1Chunk3_0_checked, root0Node30Step1Chunk3_1_checked, root0Node30Step1Chunk3_2_checked, root0Node30Step1Chunk3_3_checked, root0Node30Step1Chunk3_4_checked, root0Node30Step1Chunk3_5_checked, root0Node30Step1Chunk4_0_checked, root0Node30Step1Chunk4_1_checked, root0Node30Step1Chunk4_2_checked, root0Node30Step1Chunk4_3_checked, root0Node30Step1Chunk4_4_checked, root0Node30Step1Chunk4_5_checked, root0Node30Step1Chunk5_0_checked, root0Node30Step1Chunk5_1_checked, root0Node30Step1Chunk5_2_checked, root0Node30Step1Chunk5_3_checked, root0Node30Step1Chunk5_4_checked, root0Node30Step1Chunk5_5_checked, root0Node30Step1Chunk6_0_checked, root0Node30Step1Chunk6_1_checked, root0Node30Step1Chunk6_2_checked, root0Node30Step1Chunk6_3_checked, root0Node30Step1Chunk6_4_checked, root0Node30Step1Chunk6_5_checked, root0Node30Step1Chunk7_0_checked, root0Node30Step1Chunk7_1_checked, root0Node30Step1Chunk7_2_checked, root0Node30Step1Chunk7_3_checked, root0Node30Step1Chunk7_4_checked, root0Node30Step1Chunk7_5_checked, root0Node30Step1Chunk8_0_checked, root0Node30Step1Chunk8_1_checked, root0Node30Step1Chunk8_2_checked, root0Node30Step1Chunk8_3_checked, root0Node30Step1Chunk8_4_checked, root0Node30Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node31Domains0 : Domains 61 State := restrict root0Node30Domains1 26 (5,4)
def root0Node31Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(3,5)]
  | 3 => some [(0,3)]
  | 4 => some [(4,1)]
  | 5 => some [(4,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(2,4)]
  | 9 => some [(1,3)]
  | 10 => some [(5,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(4,3)]
  | 25 => some [(7,5)]
  | 26 => some [(5,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(1,3)]
  | 34 => some [(4,2),(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(0,3)]
  | 37 => some [(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(8,1)]
  | 41 => some [(6,5)]
  | 42 => some [(0,4)]
  | 43 => some [(4,2)]
  | 44 => some [(5,3)]
  | 45 => some [(5,5),(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(3,0),(7,0)]
  | 50 => some [(1,4),(3,4),(7,4)]
  | 51 => some [(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(0,2),(6,0)]
  | 57 => some [(1,1),(7,1)]
  | 58 => some [(4,1),(7,5)]
  | 59 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root0Node31Domains0_fast_eq : root0Node31Domains0 = expandDomains root0Node31Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node31Domains0 v = expandDomains root0Node31Domains0Fast v from by decide) v
def root0Node31Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(3,5)]
  | 3 => [(0,3)]
  | 4 => [(4,1)]
  | 5 => [(4,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(2,4)]
  | 9 => [(1,3)]
  | 10 => [(5,2)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(6,0)]
  | 14 => [(7,1)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(7,0)]
  | 24 => [(4,3)]
  | 25 => [(7,5)]
  | 26 => [(5,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(7,4)]
  | 33 => [(1,3)]
  | 34 => [(4,2),(8,2)]
  | 35 => [(7,5)]
  | 36 => [(0,3)]
  | 37 => [(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(8,1)]
  | 41 => [(6,5)]
  | 42 => [(0,4)]
  | 43 => [(4,2)]
  | 44 => [(5,3)]
  | 45 => [(5,5),(8,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(5,5),(8,5)]
  | 49 => [(3,0),(7,0)]
  | 50 => [(1,4),(3,4)]
  | 51 => [(0,5),(6,3)]
  | 52 => [(4,4),(7,2)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(0,2),(6,0)]
  | 57 => [(1,1),(7,1)]
  | 58 => [(4,1),(7,5)]
  | 59 => [(0,2),(6,0)]
  | _ => [(1,1),(7,1)]
def root0Node31Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(3,5)]
  | 3 => some [(0,3)]
  | 4 => some [(4,1)]
  | 5 => some [(4,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(2,4)]
  | 9 => some [(1,3)]
  | 10 => some [(5,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(4,3)]
  | 25 => some [(7,5)]
  | 26 => some [(5,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(1,3)]
  | 34 => some [(4,2),(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(0,3)]
  | 37 => some [(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(8,1)]
  | 41 => some [(6,5)]
  | 42 => some [(0,4)]
  | 43 => some [(4,2)]
  | 44 => some [(5,3)]
  | 45 => some [(5,5),(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(3,0),(7,0)]
  | 50 => some [(1,4),(3,4)]
  | 51 => some [(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(0,2),(6,0)]
  | 57 => some [(1,1),(7,1)]
  | 58 => some [(4,1),(7,5)]
  | 59 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root0Node31Domains1_fast_eq : root0Node31Domains1 = expandDomains root0Node31Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node31Domains1 v = expandDomains root0Node31Domains1Fast v from by decide) v
theorem root0Node31Step1Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root0Node31Domains0 root0Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node31Domains0 root0Node31Domains1
    root0Node31Domains0Fast root0Node31Domains1Fast
    root0Node31Domains0_fast_eq root0Node31Domains1_fast_eq (by decide)
theorem root0Node31Step1_checked :
    checkReplacement table26 root0Node31Domains0 root0Node31Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node31Step1Chunk0_0_checked, root0Node31Step1Chunk0_1_checked, root0Node31Step1Chunk0_2_checked, root0Node31Step1Chunk0_3_checked, root0Node31Step1Chunk0_4_checked, root0Node31Step1Chunk0_5_checked, root0Node31Step1Chunk1_0_checked, root0Node31Step1Chunk1_1_checked, root0Node31Step1Chunk1_2_checked, root0Node31Step1Chunk1_3_checked, root0Node31Step1Chunk1_4_checked, root0Node31Step1Chunk1_5_checked, root0Node31Step1Chunk2_0_checked, root0Node31Step1Chunk2_1_checked, root0Node31Step1Chunk2_2_checked, root0Node31Step1Chunk2_3_checked, root0Node31Step1Chunk2_4_checked, root0Node31Step1Chunk2_5_checked, root0Node31Step1Chunk3_0_checked, root0Node31Step1Chunk3_1_checked, root0Node31Step1Chunk3_2_checked, root0Node31Step1Chunk3_3_checked, root0Node31Step1Chunk3_4_checked, root0Node31Step1Chunk3_5_checked, root0Node31Step1Chunk4_0_checked, root0Node31Step1Chunk4_1_checked, root0Node31Step1Chunk4_2_checked, root0Node31Step1Chunk4_3_checked, root0Node31Step1Chunk4_4_checked, root0Node31Step1Chunk4_5_checked, root0Node31Step1Chunk5_0_checked, root0Node31Step1Chunk5_1_checked, root0Node31Step1Chunk5_2_checked, root0Node31Step1Chunk5_3_checked, root0Node31Step1Chunk5_4_checked, root0Node31Step1Chunk5_5_checked, root0Node31Step1Chunk6_0_checked, root0Node31Step1Chunk6_1_checked, root0Node31Step1Chunk6_2_checked, root0Node31Step1Chunk6_3_checked, root0Node31Step1Chunk6_4_checked, root0Node31Step1Chunk6_5_checked, root0Node31Step1Chunk7_0_checked, root0Node31Step1Chunk7_1_checked, root0Node31Step1Chunk7_2_checked, root0Node31Step1Chunk7_3_checked, root0Node31Step1Chunk7_4_checked, root0Node31Step1Chunk7_5_checked, root0Node31Step1Chunk8_0_checked, root0Node31Step1Chunk8_1_checked, root0Node31Step1Chunk8_2_checked, root0Node31Step1Chunk8_3_checked, root0Node31Step1Chunk8_4_checked, root0Node31Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node32Domains0 : Domains 61 State := restrict root0Node31Domains1 34 (4,2)
def root0Node32Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(3,5)]
  | 3 => some [(0,3)]
  | 4 => some [(4,1)]
  | 5 => some [(4,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(2,4)]
  | 9 => some [(1,3)]
  | 10 => some [(5,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(4,3)]
  | 25 => some [(7,5)]
  | 26 => some [(5,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(1,3)]
  | 34 => some [(4,2)]
  | 35 => some [(7,5)]
  | 36 => some [(0,3)]
  | 37 => some [(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(8,1)]
  | 41 => some [(6,5)]
  | 42 => some [(0,4)]
  | 43 => some [(4,2)]
  | 44 => some [(5,3)]
  | 45 => some [(5,5),(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(3,0),(7,0)]
  | 50 => some [(1,4),(3,4)]
  | 51 => some [(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(0,2),(6,0)]
  | 57 => some [(1,1),(7,1)]
  | 58 => some [(4,1),(7,5)]
  | 59 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root0Node32Domains0_fast_eq : root0Node32Domains0 = expandDomains root0Node32Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node32Domains0 v = expandDomains root0Node32Domains0Fast v from by decide) v
def root0Node32Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(3,5)]
  | 3 => [(0,3)]
  | 4 => [(4,1)]
  | 5 => [(4,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(2,4)]
  | 9 => [(1,3)]
  | 10 => [(5,2)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(6,0)]
  | 14 => [(7,1)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(7,0)]
  | 24 => [(4,3)]
  | 25 => [(7,5)]
  | 26 => [(5,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(7,4)]
  | 33 => [(1,3)]
  | 34 => [(4,2)]
  | 35 => [(7,5)]
  | 36 => [(0,3)]
  | 37 => [(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(8,1)]
  | 41 => [(6,5)]
  | 42 => [(0,4)]
  | 43 => [(4,2)]
  | 44 => [(5,3)]
  | 45 => [(5,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(5,5)]
  | 49 => [(3,0),(7,0)]
  | 50 => [(1,4),(3,4)]
  | 51 => [(0,5),(6,3)]
  | 52 => [(4,4)]
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(0,2),(6,0)]
  | 57 => [(1,1),(7,1)]
  | 58 => [(7,5)]
  | 59 => [(6,0)]
  | _ => [(7,1)]
def root0Node32Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(3,5)]
  | 3 => some [(0,3)]
  | 4 => some [(4,1)]
  | 5 => some [(4,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(2,4)]
  | 9 => some [(1,3)]
  | 10 => some [(5,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(4,3)]
  | 25 => some [(7,5)]
  | 26 => some [(5,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(1,3)]
  | 34 => some [(4,2)]
  | 35 => some [(7,5)]
  | 36 => some [(0,3)]
  | 37 => some [(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(8,1)]
  | 41 => some [(6,5)]
  | 42 => some [(0,4)]
  | 43 => some [(4,2)]
  | 44 => some [(5,3)]
  | 45 => some [(5,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5)]
  | 49 => some [(3,0),(7,0)]
  | 50 => some [(1,4),(3,4)]
  | 51 => some [(0,5),(6,3)]
  | 52 => some [(4,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(0,2),(6,0)]
  | 57 => some [(1,1),(7,1)]
  | 58 => some [(7,5)]
  | 59 => some [(6,0)]
  | _ => some [(7,1)]
theorem root0Node32Domains1_fast_eq : root0Node32Domains1 = expandDomains root0Node32Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node32Domains1 v = expandDomains root0Node32Domains1Fast v from by decide) v
theorem root0Node32Step1Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root0Node32Domains0 root0Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains0 root0Node32Domains1
    root0Node32Domains0Fast root0Node32Domains1Fast
    root0Node32Domains0_fast_eq root0Node32Domains1_fast_eq (by decide)
theorem root0Node32Step1_checked :
    checkReplacement table40 root0Node32Domains0 root0Node32Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node32Step1Chunk0_0_checked, root0Node32Step1Chunk0_1_checked, root0Node32Step1Chunk0_2_checked, root0Node32Step1Chunk0_3_checked, root0Node32Step1Chunk0_4_checked, root0Node32Step1Chunk0_5_checked, root0Node32Step1Chunk1_0_checked, root0Node32Step1Chunk1_1_checked, root0Node32Step1Chunk1_2_checked, root0Node32Step1Chunk1_3_checked, root0Node32Step1Chunk1_4_checked, root0Node32Step1Chunk1_5_checked, root0Node32Step1Chunk2_0_checked, root0Node32Step1Chunk2_1_checked, root0Node32Step1Chunk2_2_checked, root0Node32Step1Chunk2_3_checked, root0Node32Step1Chunk2_4_checked, root0Node32Step1Chunk2_5_checked, root0Node32Step1Chunk3_0_checked, root0Node32Step1Chunk3_1_checked, root0Node32Step1Chunk3_2_checked, root0Node32Step1Chunk3_3_checked, root0Node32Step1Chunk3_4_checked, root0Node32Step1Chunk3_5_checked, root0Node32Step1Chunk4_0_checked, root0Node32Step1Chunk4_1_checked, root0Node32Step1Chunk4_2_checked, root0Node32Step1Chunk4_3_checked, root0Node32Step1Chunk4_4_checked, root0Node32Step1Chunk4_5_checked, root0Node32Step1Chunk5_0_checked, root0Node32Step1Chunk5_1_checked, root0Node32Step1Chunk5_2_checked, root0Node32Step1Chunk5_3_checked, root0Node32Step1Chunk5_4_checked, root0Node32Step1Chunk5_5_checked, root0Node32Step1Chunk6_0_checked, root0Node32Step1Chunk6_1_checked, root0Node32Step1Chunk6_2_checked, root0Node32Step1Chunk6_3_checked, root0Node32Step1Chunk6_4_checked, root0Node32Step1Chunk6_5_checked, root0Node32Step1Chunk7_0_checked, root0Node32Step1Chunk7_1_checked, root0Node32Step1Chunk7_2_checked, root0Node32Step1Chunk7_3_checked, root0Node32Step1Chunk7_4_checked, root0Node32Step1Chunk7_5_checked, root0Node32Step1Chunk8_0_checked, root0Node32Step1Chunk8_1_checked, root0Node32Step1Chunk8_2_checked, root0Node32Step1Chunk8_3_checked, root0Node32Step1Chunk8_4_checked, root0Node32Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node32Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(3,5)]
  | 3 => [(0,3)]
  | 4 => [(4,1)]
  | 5 => [(4,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(2,4)]
  | 9 => [(1,3)]
  | 10 => [(5,2)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(6,0)]
  | 14 => [(7,1)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(7,0)]
  | 24 => [(4,3)]
  | 25 => [(7,5)]
  | 26 => [(5,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(7,4)]
  | 33 => [(1,3)]
  | 34 => [(4,2)]
  | 35 => [(7,5)]
  | 36 => [(0,3)]
  | 37 => [(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(8,1)]
  | 41 => [(6,5)]
  | 42 => [(0,4)]
  | 43 => [(4,2)]
  | 44 => [(5,3)]
  | 45 => [(5,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(5,5)]
  | 49 => [(3,0),(7,0)]
  | 50 => [(1,4)]
  | 51 => [(0,5)]
  | 52 => [(4,4)]
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(6,0)]
  | 57 => [(7,1)]
  | 58 => [(7,5)]
  | 59 => [(6,0)]
  | _ => [(7,1)]
def root0Node32Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(3,5)]
  | 3 => some [(0,3)]
  | 4 => some [(4,1)]
  | 5 => some [(4,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(2,4)]
  | 9 => some [(1,3)]
  | 10 => some [(5,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(4,3)]
  | 25 => some [(7,5)]
  | 26 => some [(5,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(1,3)]
  | 34 => some [(4,2)]
  | 35 => some [(7,5)]
  | 36 => some [(0,3)]
  | 37 => some [(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(8,1)]
  | 41 => some [(6,5)]
  | 42 => some [(0,4)]
  | 43 => some [(4,2)]
  | 44 => some [(5,3)]
  | 45 => some [(5,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5)]
  | 49 => some [(3,0),(7,0)]
  | 50 => some [(1,4)]
  | 51 => some [(0,5)]
  | 52 => some [(4,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(6,0)]
  | 57 => some [(7,1)]
  | 58 => some [(7,5)]
  | 59 => some [(6,0)]
  | _ => some [(7,1)]
theorem root0Node32Domains2_fast_eq : root0Node32Domains2 = expandDomains root0Node32Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node32Domains2 v = expandDomains root0Node32Domains2Fast v from by decide) v
theorem root0Node32Step2Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root0Node32Domains1 root0Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node32Domains1 root0Node32Domains2
    root0Node32Domains1Fast root0Node32Domains2Fast
    root0Node32Domains1_fast_eq root0Node32Domains2_fast_eq (by decide)
theorem root0Node32Step2_checked :
    checkReplacement table36 root0Node32Domains1 root0Node32Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node32Step2Chunk0_0_checked, root0Node32Step2Chunk0_1_checked, root0Node32Step2Chunk0_2_checked, root0Node32Step2Chunk0_3_checked, root0Node32Step2Chunk0_4_checked, root0Node32Step2Chunk0_5_checked, root0Node32Step2Chunk1_0_checked, root0Node32Step2Chunk1_1_checked, root0Node32Step2Chunk1_2_checked, root0Node32Step2Chunk1_3_checked, root0Node32Step2Chunk1_4_checked, root0Node32Step2Chunk1_5_checked, root0Node32Step2Chunk2_0_checked, root0Node32Step2Chunk2_1_checked, root0Node32Step2Chunk2_2_checked, root0Node32Step2Chunk2_3_checked, root0Node32Step2Chunk2_4_checked, root0Node32Step2Chunk2_5_checked, root0Node32Step2Chunk3_0_checked, root0Node32Step2Chunk3_1_checked, root0Node32Step2Chunk3_2_checked, root0Node32Step2Chunk3_3_checked, root0Node32Step2Chunk3_4_checked, root0Node32Step2Chunk3_5_checked, root0Node32Step2Chunk4_0_checked, root0Node32Step2Chunk4_1_checked, root0Node32Step2Chunk4_2_checked, root0Node32Step2Chunk4_3_checked, root0Node32Step2Chunk4_4_checked, root0Node32Step2Chunk4_5_checked, root0Node32Step2Chunk5_0_checked, root0Node32Step2Chunk5_1_checked, root0Node32Step2Chunk5_2_checked, root0Node32Step2Chunk5_3_checked, root0Node32Step2Chunk5_4_checked, root0Node32Step2Chunk5_5_checked, root0Node32Step2Chunk6_0_checked, root0Node32Step2Chunk6_1_checked, root0Node32Step2Chunk6_2_checked, root0Node32Step2Chunk6_3_checked, root0Node32Step2Chunk6_4_checked, root0Node32Step2Chunk6_5_checked, root0Node32Step2Chunk7_0_checked, root0Node32Step2Chunk7_1_checked, root0Node32Step2Chunk7_2_checked, root0Node32Step2Chunk7_3_checked, root0Node32Step2Chunk7_4_checked, root0Node32Step2Chunk7_5_checked, root0Node32Step2Chunk8_0_checked, root0Node32Step2Chunk8_1_checked, root0Node32Step2Chunk8_2_checked, root0Node32Step2Chunk8_3_checked, root0Node32Step2Chunk8_4_checked, root0Node32Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
