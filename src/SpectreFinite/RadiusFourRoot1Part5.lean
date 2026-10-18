module

public import SpectreFinite.RadiusFourRoot1Part4
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable35
public import SpectreFinite.RadiusFourTable37
public import SpectreFinite.RadiusFourTable40

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node12Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(4,3)]
  | 6 => [(1,5)]
  | 7 => [(6,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(2,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(7,3),(8,3)]
  | 18 => [(7,5)]
  | 19 => [(6,0)]
  | 20 => [(3,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(1,4),(6,4)]
  | 25 => [(0,5),(1,2)]
  | 26 => [(4,5),(7,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(0,3),(6,0)]
  | 34 => [(7,1),(8,1)]
  | 35 => [(1,2),(6,2),(7,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(4,2),(8,2)]
  | 42 => [(5,0),(5,3),(8,0)]
  | 43 => [(4,1),(7,1),(8,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(7,4),(8,4)]
  | 50 => [(4,5),(5,2),(5,5),(8,5)]
  | 51 => [(7,0),(8,0)]
  | 52 => [(8,3)]
  | 53 => [(5,5),(8,5)]
  | 54 => [(1,0)]
  | 55 => [(2,1),(7,1)]
  | 56 => [(4,4),(5,4),(7,2),(8,4)]
  | 57 => [(1,4),(7,4)]
  | 58 => [(0,5),(1,3),(6,3)]
  | 59 => [(4,4),(7,2),(8,2)]
  | _ => [(0,0),(4,0),(5,0),(8,0)]
def root1Node12Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(1,5)]
  | 7 => some [(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3),(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(3,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4),(6,4)]
  | 25 => some [(0,5),(1,2)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3),(6,0)]
  | 34 => some [(7,1),(8,1)]
  | 35 => some [(1,2),(6,2),(7,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2),(8,2)]
  | 42 => some [(5,0),(5,3),(8,0)]
  | 43 => some [(4,1),(7,1),(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(4,5),(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5),(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(2,1),(7,1)]
  | 56 => some [(4,4),(5,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(1,3),(6,3)]
  | 59 => some [(4,4),(7,2),(8,2)]
  | _ => some [(0,0),(4,0),(5,0),(8,0)]
theorem root1Node12Domains2_fast_eq : root1Node12Domains2 = expandDomains root1Node12Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node12Domains2 v = expandDomains root1Node12Domains2Fast v from by decide) v
theorem root1Node12Step2Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root1Node12Domains1 root1Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains1 root1Node12Domains2
    root1Node12Domains1Fast root1Node12Domains2Fast
    root1Node12Domains1_fast_eq root1Node12Domains2_fast_eq (by decide)
theorem root1Node12Step2_checked :
    checkReplacement table40 root1Node12Domains1 root1Node12Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node12Step2Chunk0_0_checked, root1Node12Step2Chunk0_1_checked, root1Node12Step2Chunk0_2_checked, root1Node12Step2Chunk0_3_checked, root1Node12Step2Chunk0_4_checked, root1Node12Step2Chunk0_5_checked, root1Node12Step2Chunk1_0_checked, root1Node12Step2Chunk1_1_checked, root1Node12Step2Chunk1_2_checked, root1Node12Step2Chunk1_3_checked, root1Node12Step2Chunk1_4_checked, root1Node12Step2Chunk1_5_checked, root1Node12Step2Chunk2_0_checked, root1Node12Step2Chunk2_1_checked, root1Node12Step2Chunk2_2_checked, root1Node12Step2Chunk2_3_checked, root1Node12Step2Chunk2_4_checked, root1Node12Step2Chunk2_5_checked, root1Node12Step2Chunk3_0_checked, root1Node12Step2Chunk3_1_checked, root1Node12Step2Chunk3_2_checked, root1Node12Step2Chunk3_3_checked, root1Node12Step2Chunk3_4_checked, root1Node12Step2Chunk3_5_checked, root1Node12Step2Chunk4_0_checked, root1Node12Step2Chunk4_1_checked, root1Node12Step2Chunk4_2_checked, root1Node12Step2Chunk4_3_checked, root1Node12Step2Chunk4_4_checked, root1Node12Step2Chunk4_5_checked, root1Node12Step2Chunk5_0_checked, root1Node12Step2Chunk5_1_checked, root1Node12Step2Chunk5_2_checked, root1Node12Step2Chunk5_3_checked, root1Node12Step2Chunk5_4_checked, root1Node12Step2Chunk5_5_checked, root1Node12Step2Chunk6_0_checked, root1Node12Step2Chunk6_1_checked, root1Node12Step2Chunk6_2_checked, root1Node12Step2Chunk6_3_checked, root1Node12Step2Chunk6_4_checked, root1Node12Step2Chunk6_5_checked, root1Node12Step2Chunk7_0_checked, root1Node12Step2Chunk7_1_checked, root1Node12Step2Chunk7_2_checked, root1Node12Step2Chunk7_3_checked, root1Node12Step2Chunk7_4_checked, root1Node12Step2Chunk7_5_checked, root1Node12Step2Chunk8_0_checked, root1Node12Step2Chunk8_1_checked, root1Node12Step2Chunk8_2_checked, root1Node12Step2Chunk8_3_checked, root1Node12Step2Chunk8_4_checked, root1Node12Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node12Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(4,3)]
  | 6 => [(1,5)]
  | 7 => [(6,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(2,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(7,3),(8,3)]
  | 18 => [(7,5)]
  | 19 => [(6,0)]
  | 20 => [(3,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(1,4),(6,4)]
  | 25 => [(0,5),(1,2)]
  | 26 => [(7,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(0,3),(6,0)]
  | 34 => [(7,1),(8,1)]
  | 35 => [(1,2),(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(4,2),(8,2)]
  | 42 => [(5,0),(5,3),(8,0)]
  | 43 => [(7,1),(8,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(7,4),(8,4)]
  | 50 => [(4,5),(5,5),(8,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(5,5),(8,5)]
  | 54 => [(1,0)]
  | 55 => [(2,1),(7,1)]
  | 56 => [(4,4),(7,2)]
  | 57 => [(1,4),(7,4)]
  | 58 => [(0,5),(1,3),(6,3)]
  | 59 => [(4,4),(7,2),(8,2)]
  | _ => [(0,0),(4,0),(5,0),(8,0)]
def root1Node12Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(1,5)]
  | 7 => some [(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3),(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(3,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4),(6,4)]
  | 25 => some [(0,5),(1,2)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3),(6,0)]
  | 34 => some [(7,1),(8,1)]
  | 35 => some [(1,2),(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2),(8,2)]
  | 42 => some [(5,0),(5,3),(8,0)]
  | 43 => some [(7,1),(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(4,5),(5,5),(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5),(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(2,1),(7,1)]
  | 56 => some [(4,4),(7,2)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(1,3),(6,3)]
  | 59 => some [(4,4),(7,2),(8,2)]
  | _ => some [(0,0),(4,0),(5,0),(8,0)]
theorem root1Node12Domains3_fast_eq : root1Node12Domains3 = expandDomains root1Node12Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node12Domains3 v = expandDomains root1Node12Domains3Fast v from by decide) v
theorem root1Node12Step3Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root1Node12Domains2 root1Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node12Domains2 root1Node12Domains3
    root1Node12Domains2Fast root1Node12Domains3Fast
    root1Node12Domains2_fast_eq root1Node12Domains3_fast_eq (by decide)
theorem root1Node12Step3_checked :
    checkReplacement table35 root1Node12Domains2 root1Node12Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node12Step3Chunk0_0_checked, root1Node12Step3Chunk0_1_checked, root1Node12Step3Chunk0_2_checked, root1Node12Step3Chunk0_3_checked, root1Node12Step3Chunk0_4_checked, root1Node12Step3Chunk0_5_checked, root1Node12Step3Chunk1_0_checked, root1Node12Step3Chunk1_1_checked, root1Node12Step3Chunk1_2_checked, root1Node12Step3Chunk1_3_checked, root1Node12Step3Chunk1_4_checked, root1Node12Step3Chunk1_5_checked, root1Node12Step3Chunk2_0_checked, root1Node12Step3Chunk2_1_checked, root1Node12Step3Chunk2_2_checked, root1Node12Step3Chunk2_3_checked, root1Node12Step3Chunk2_4_checked, root1Node12Step3Chunk2_5_checked, root1Node12Step3Chunk3_0_checked, root1Node12Step3Chunk3_1_checked, root1Node12Step3Chunk3_2_checked, root1Node12Step3Chunk3_3_checked, root1Node12Step3Chunk3_4_checked, root1Node12Step3Chunk3_5_checked, root1Node12Step3Chunk4_0_checked, root1Node12Step3Chunk4_1_checked, root1Node12Step3Chunk4_2_checked, root1Node12Step3Chunk4_3_checked, root1Node12Step3Chunk4_4_checked, root1Node12Step3Chunk4_5_checked, root1Node12Step3Chunk5_0_checked, root1Node12Step3Chunk5_1_checked, root1Node12Step3Chunk5_2_checked, root1Node12Step3Chunk5_3_checked, root1Node12Step3Chunk5_4_checked, root1Node12Step3Chunk5_5_checked, root1Node12Step3Chunk6_0_checked, root1Node12Step3Chunk6_1_checked, root1Node12Step3Chunk6_2_checked, root1Node12Step3Chunk6_3_checked, root1Node12Step3Chunk6_4_checked, root1Node12Step3Chunk6_5_checked, root1Node12Step3Chunk7_0_checked, root1Node12Step3Chunk7_1_checked, root1Node12Step3Chunk7_2_checked, root1Node12Step3Chunk7_3_checked, root1Node12Step3Chunk7_4_checked, root1Node12Step3Chunk7_5_checked, root1Node12Step3Chunk8_0_checked, root1Node12Step3Chunk8_1_checked, root1Node12Step3Chunk8_2_checked, root1Node12Step3Chunk8_3_checked, root1Node12Step3Chunk8_4_checked, root1Node12Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node13Domains0 : Domains 61 State := restrict root1Node12Domains3 17 (7,3)
def root1Node13Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(1,5)]
  | 7 => some [(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(3,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4),(6,4)]
  | 25 => some [(0,5),(1,2)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3),(6,0)]
  | 34 => some [(7,1),(8,1)]
  | 35 => some [(1,2),(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2),(8,2)]
  | 42 => some [(5,0),(5,3),(8,0)]
  | 43 => some [(7,1),(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(4,5),(5,5),(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5),(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(2,1),(7,1)]
  | 56 => some [(4,4),(7,2)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(1,3),(6,3)]
  | 59 => some [(4,4),(7,2),(8,2)]
  | _ => some [(0,0),(4,0),(5,0),(8,0)]
theorem root1Node13Domains0_fast_eq : root1Node13Domains0 = expandDomains root1Node13Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node13Domains0 v = expandDomains root1Node13Domains0Fast v from by decide) v
def root1Node13Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(4,3)]
  | 6 => [(1,5)]
  | 7 => [(6,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(2,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(7,3)]
  | 18 => [(7,5)]
  | 19 => [(6,0)]
  | 20 => [(3,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(7,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(0,3)]
  | 34 => [(8,1)]
  | 35 => [(1,2),(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(4,2)]
  | 42 => [(5,3)]
  | 43 => [(7,1),(8,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(7,4)]
  | 50 => [(4,5),(5,5),(8,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(5,5)]
  | 54 => [(1,0)]
  | 55 => [(2,1)]
  | 56 => [(4,4),(7,2)]
  | 57 => [(1,4),(7,4)]
  | 58 => [(0,5)]
  | 59 => [(4,4)]
  | _ => [(0,0)]
def root1Node13Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(1,5)]
  | 7 => some [(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(3,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(8,1)]
  | 35 => some [(1,2),(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(7,1),(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(7,4)]
  | 50 => some [(4,5),(5,5),(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5)]
  | 54 => some [(1,0)]
  | 55 => some [(2,1)]
  | 56 => some [(4,4),(7,2)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5)]
  | 59 => some [(4,4)]
  | _ => some [(0,0)]
theorem root1Node13Domains1_fast_eq : root1Node13Domains1 = expandDomains root1Node13Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node13Domains1 v = expandDomains root1Node13Domains1Fast v from by decide) v
theorem root1Node13Step1Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root1Node13Domains0 root1Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains0 root1Node13Domains1
    root1Node13Domains0Fast root1Node13Domains1Fast
    root1Node13Domains0_fast_eq root1Node13Domains1_fast_eq (by decide)
theorem root1Node13Step1_checked :
    checkReplacement table40 root1Node13Domains0 root1Node13Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node13Step1Chunk0_0_checked, root1Node13Step1Chunk0_1_checked, root1Node13Step1Chunk0_2_checked, root1Node13Step1Chunk0_3_checked, root1Node13Step1Chunk0_4_checked, root1Node13Step1Chunk0_5_checked, root1Node13Step1Chunk1_0_checked, root1Node13Step1Chunk1_1_checked, root1Node13Step1Chunk1_2_checked, root1Node13Step1Chunk1_3_checked, root1Node13Step1Chunk1_4_checked, root1Node13Step1Chunk1_5_checked, root1Node13Step1Chunk2_0_checked, root1Node13Step1Chunk2_1_checked, root1Node13Step1Chunk2_2_checked, root1Node13Step1Chunk2_3_checked, root1Node13Step1Chunk2_4_checked, root1Node13Step1Chunk2_5_checked, root1Node13Step1Chunk3_0_checked, root1Node13Step1Chunk3_1_checked, root1Node13Step1Chunk3_2_checked, root1Node13Step1Chunk3_3_checked, root1Node13Step1Chunk3_4_checked, root1Node13Step1Chunk3_5_checked, root1Node13Step1Chunk4_0_checked, root1Node13Step1Chunk4_1_checked, root1Node13Step1Chunk4_2_checked, root1Node13Step1Chunk4_3_checked, root1Node13Step1Chunk4_4_checked, root1Node13Step1Chunk4_5_checked, root1Node13Step1Chunk5_0_checked, root1Node13Step1Chunk5_1_checked, root1Node13Step1Chunk5_2_checked, root1Node13Step1Chunk5_3_checked, root1Node13Step1Chunk5_4_checked, root1Node13Step1Chunk5_5_checked, root1Node13Step1Chunk6_0_checked, root1Node13Step1Chunk6_1_checked, root1Node13Step1Chunk6_2_checked, root1Node13Step1Chunk6_3_checked, root1Node13Step1Chunk6_4_checked, root1Node13Step1Chunk6_5_checked, root1Node13Step1Chunk7_0_checked, root1Node13Step1Chunk7_1_checked, root1Node13Step1Chunk7_2_checked, root1Node13Step1Chunk7_3_checked, root1Node13Step1Chunk7_4_checked, root1Node13Step1Chunk7_5_checked, root1Node13Step1Chunk8_0_checked, root1Node13Step1Chunk8_1_checked, root1Node13Step1Chunk8_2_checked, root1Node13Step1Chunk8_3_checked, root1Node13Step1Chunk8_4_checked, root1Node13Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node13Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(4,3)]
  | 6 => [(1,5)]
  | 7 => [(6,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(2,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(7,3)]
  | 18 => [(7,5)]
  | 19 => [(6,0)]
  | 20 => [(3,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(7,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(0,3)]
  | 34 => [(8,1)]
  | 35 => [(1,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(4,2)]
  | 42 => [(5,3)]
  | 43 => [(8,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(7,4)]
  | 50 => [(5,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(5,5)]
  | 54 => [(1,0)]
  | 55 => [(2,1)]
  | 56 => [(4,4)]
  | 57 => [(1,4)]
  | 58 => [(0,5)]
  | 59 => [(4,4)]
  | _ => [(0,0)]
def root1Node13Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(1,5)]
  | 7 => some [(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(3,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(8,1)]
  | 35 => some [(1,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5)]
  | 54 => some [(1,0)]
  | 55 => some [(2,1)]
  | 56 => some [(4,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(4,4)]
  | _ => some [(0,0)]
theorem root1Node13Domains2_fast_eq : root1Node13Domains2 = expandDomains root1Node13Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node13Domains2 v = expandDomains root1Node13Domains2Fast v from by decide) v
theorem root1Node13Step2Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root1Node13Domains1 root1Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node13Domains1 root1Node13Domains2
    root1Node13Domains1Fast root1Node13Domains2Fast
    root1Node13Domains1_fast_eq root1Node13Domains2_fast_eq (by decide)
theorem root1Node13Step2_checked :
    checkReplacement table37 root1Node13Domains1 root1Node13Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node13Step2Chunk0_0_checked, root1Node13Step2Chunk0_1_checked, root1Node13Step2Chunk0_2_checked, root1Node13Step2Chunk0_3_checked, root1Node13Step2Chunk0_4_checked, root1Node13Step2Chunk0_5_checked, root1Node13Step2Chunk1_0_checked, root1Node13Step2Chunk1_1_checked, root1Node13Step2Chunk1_2_checked, root1Node13Step2Chunk1_3_checked, root1Node13Step2Chunk1_4_checked, root1Node13Step2Chunk1_5_checked, root1Node13Step2Chunk2_0_checked, root1Node13Step2Chunk2_1_checked, root1Node13Step2Chunk2_2_checked, root1Node13Step2Chunk2_3_checked, root1Node13Step2Chunk2_4_checked, root1Node13Step2Chunk2_5_checked, root1Node13Step2Chunk3_0_checked, root1Node13Step2Chunk3_1_checked, root1Node13Step2Chunk3_2_checked, root1Node13Step2Chunk3_3_checked, root1Node13Step2Chunk3_4_checked, root1Node13Step2Chunk3_5_checked, root1Node13Step2Chunk4_0_checked, root1Node13Step2Chunk4_1_checked, root1Node13Step2Chunk4_2_checked, root1Node13Step2Chunk4_3_checked, root1Node13Step2Chunk4_4_checked, root1Node13Step2Chunk4_5_checked, root1Node13Step2Chunk5_0_checked, root1Node13Step2Chunk5_1_checked, root1Node13Step2Chunk5_2_checked, root1Node13Step2Chunk5_3_checked, root1Node13Step2Chunk5_4_checked, root1Node13Step2Chunk5_5_checked, root1Node13Step2Chunk6_0_checked, root1Node13Step2Chunk6_1_checked, root1Node13Step2Chunk6_2_checked, root1Node13Step2Chunk6_3_checked, root1Node13Step2Chunk6_4_checked, root1Node13Step2Chunk6_5_checked, root1Node13Step2Chunk7_0_checked, root1Node13Step2Chunk7_1_checked, root1Node13Step2Chunk7_2_checked, root1Node13Step2Chunk7_3_checked, root1Node13Step2Chunk7_4_checked, root1Node13Step2Chunk7_5_checked, root1Node13Step2Chunk8_0_checked, root1Node13Step2Chunk8_1_checked, root1Node13Step2Chunk8_2_checked, root1Node13Step2Chunk8_3_checked, root1Node13Step2Chunk8_4_checked, root1Node13Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root1Node13Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node13Domains2 (.output 5) = true := by decide
def root1Node14Domains0 : Domains 61 State := restrict root1Node12Domains3 17 (8,3)
def root1Node14Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(1,5)]
  | 7 => some [(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(3,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4),(6,4)]
  | 25 => some [(0,5),(1,2)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3),(6,0)]
  | 34 => some [(7,1),(8,1)]
  | 35 => some [(1,2),(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2),(8,2)]
  | 42 => some [(5,0),(5,3),(8,0)]
  | 43 => some [(7,1),(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(4,5),(5,5),(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5),(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(2,1),(7,1)]
  | 56 => some [(4,4),(7,2)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(1,3),(6,3)]
  | 59 => some [(4,4),(7,2),(8,2)]
  | _ => some [(0,0),(4,0),(5,0),(8,0)]
theorem root1Node14Domains0_fast_eq : root1Node14Domains0 = expandDomains root1Node14Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node14Domains0 v = expandDomains root1Node14Domains0Fast v from by decide) v
def root1Node14Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(4,3)]
  | 6 => [(1,5)]
  | 7 => [(6,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(2,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(8,3)]
  | 18 => [(7,5)]
  | 19 => [(6,0)]
  | 20 => [(3,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(7,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(6,0)]
  | 34 => [(7,1)]
  | 35 => [(1,2),(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(8,2)]
  | 42 => [(5,0),(8,0)]
  | 43 => [(7,1),(8,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(4,5),(5,5),(8,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(8,5)]
  | 54 => [(1,0)]
  | 55 => [(7,1)]
  | 56 => [(4,4),(7,2)]
  | 57 => [(1,4),(7,4)]
  | 58 => [(1,3),(6,3)]
  | 59 => [(7,2),(8,2)]
  | _ => [(4,0),(5,0),(8,0)]
def root1Node14Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(1,5)]
  | 7 => some [(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(3,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,2),(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0),(8,0)]
  | 43 => some [(7,1),(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(4,5),(5,5),(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(4,4),(7,2)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(1,3),(6,3)]
  | 59 => some [(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root1Node14Domains1_fast_eq : root1Node14Domains1 = expandDomains root1Node14Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node14Domains1 v = expandDomains root1Node14Domains1Fast v from by decide) v
theorem root1Node14Step1Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root1Node14Domains0 root1Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node14Domains0 root1Node14Domains1
    root1Node14Domains0Fast root1Node14Domains1Fast
    root1Node14Domains0_fast_eq root1Node14Domains1_fast_eq (by decide)
theorem root1Node14Step1_checked :
    checkReplacement table40 root1Node14Domains0 root1Node14Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node14Step1Chunk0_0_checked, root1Node14Step1Chunk0_1_checked, root1Node14Step1Chunk0_2_checked, root1Node14Step1Chunk0_3_checked, root1Node14Step1Chunk0_4_checked, root1Node14Step1Chunk0_5_checked, root1Node14Step1Chunk1_0_checked, root1Node14Step1Chunk1_1_checked, root1Node14Step1Chunk1_2_checked, root1Node14Step1Chunk1_3_checked, root1Node14Step1Chunk1_4_checked, root1Node14Step1Chunk1_5_checked, root1Node14Step1Chunk2_0_checked, root1Node14Step1Chunk2_1_checked, root1Node14Step1Chunk2_2_checked, root1Node14Step1Chunk2_3_checked, root1Node14Step1Chunk2_4_checked, root1Node14Step1Chunk2_5_checked, root1Node14Step1Chunk3_0_checked, root1Node14Step1Chunk3_1_checked, root1Node14Step1Chunk3_2_checked, root1Node14Step1Chunk3_3_checked, root1Node14Step1Chunk3_4_checked, root1Node14Step1Chunk3_5_checked, root1Node14Step1Chunk4_0_checked, root1Node14Step1Chunk4_1_checked, root1Node14Step1Chunk4_2_checked, root1Node14Step1Chunk4_3_checked, root1Node14Step1Chunk4_4_checked, root1Node14Step1Chunk4_5_checked, root1Node14Step1Chunk5_0_checked, root1Node14Step1Chunk5_1_checked, root1Node14Step1Chunk5_2_checked, root1Node14Step1Chunk5_3_checked, root1Node14Step1Chunk5_4_checked, root1Node14Step1Chunk5_5_checked, root1Node14Step1Chunk6_0_checked, root1Node14Step1Chunk6_1_checked, root1Node14Step1Chunk6_2_checked, root1Node14Step1Chunk6_3_checked, root1Node14Step1Chunk6_4_checked, root1Node14Step1Chunk6_5_checked, root1Node14Step1Chunk7_0_checked, root1Node14Step1Chunk7_1_checked, root1Node14Step1Chunk7_2_checked, root1Node14Step1Chunk7_3_checked, root1Node14Step1Chunk7_4_checked, root1Node14Step1Chunk7_5_checked, root1Node14Step1Chunk8_0_checked, root1Node14Step1Chunk8_1_checked, root1Node14Step1Chunk8_2_checked, root1Node14Step1Chunk8_3_checked, root1Node14Step1Chunk8_4_checked, root1Node14Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
