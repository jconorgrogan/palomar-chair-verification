module

public import SpectreFinite.RadiusFourRoot1Part17
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable11
public import SpectreFinite.RadiusFourTable16
public import SpectreFinite.RadiusFourTable35
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node51Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(4,5),(8,5)]
  | 6 => [(1,0)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(0,0),(6,3)]
  | 12 => [(7,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(0,2),(1,5)]
  | 19 => [(1,1),(6,1)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(7,4)]
  | 24 => [(6,3)]
  | 25 => [(7,2)]
  | 26 => [(4,5),(5,2),(5,5),(8,5)]
  | 27 => [(7,0),(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(1,0)]
  | 31 => [(2,1)]
  | 32 => [(0,2)]
  | 33 => [(1,1)]
  | 34 => [(4,1),(8,1)]
  | 35 => [(4,4),(5,4),(7,2),(8,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(0,0)]
  | 40 => [(3,2)]
  | 41 => [(4,0)]
  | 42 => [(5,3),(7,3),(8,3)]
  | 43 => [(7,5)]
  | 44 => [(6,0)]
  | 45 => [(7,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1)]
  | 49 => [(0,1)]
  | 50 => [(8,2)]
  | 51 => [(5,0)]
  | 52 => [(4,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(8,5)]
  | 56 => [(5,4),(8,4)]
  | 57 => [(0,0)]
  | 58 => [(7,2)]
  | 59 => [(7,4)]
  | _ => [(1,3),(6,3)]
def root1Node51Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(1,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(7,4)]
  | 24 => some [(6,3)]
  | 25 => some [(7,2)]
  | 26 => some [(4,5),(5,2),(5,5),(8,5)]
  | 27 => some [(7,0),(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(1,0)]
  | 31 => some [(2,1)]
  | 32 => some [(0,2)]
  | 33 => some [(1,1)]
  | 34 => some [(4,1),(8,1)]
  | 35 => some [(4,4),(5,4),(7,2),(8,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(0,0)]
  | 40 => some [(3,2)]
  | 41 => some [(4,0)]
  | 42 => some [(5,3),(7,3),(8,3)]
  | 43 => some [(7,5)]
  | 44 => some [(6,0)]
  | 45 => some [(7,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(8,2)]
  | 51 => some [(5,0)]
  | 52 => some [(4,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(0,0)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(1,3),(6,3)]
theorem root1Node51Domains2_fast_eq : root1Node51Domains2 = expandDomains root1Node51Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node51Domains2 v = expandDomains root1Node51Domains2Fast v from by decide) v
theorem root1Node51Step2Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root1Node51Domains1 root1Node51Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains1 root1Node51Domains2
    root1Node51Domains1Fast root1Node51Domains2Fast
    root1Node51Domains1_fast_eq root1Node51Domains2_fast_eq (by decide)
theorem root1Node51Step2_checked :
    checkReplacement table46 root1Node51Domains1 root1Node51Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node51Step2Chunk0_0_checked, root1Node51Step2Chunk0_1_checked, root1Node51Step2Chunk0_2_checked, root1Node51Step2Chunk0_3_checked, root1Node51Step2Chunk0_4_checked, root1Node51Step2Chunk0_5_checked, root1Node51Step2Chunk1_0_checked, root1Node51Step2Chunk1_1_checked, root1Node51Step2Chunk1_2_checked, root1Node51Step2Chunk1_3_checked, root1Node51Step2Chunk1_4_checked, root1Node51Step2Chunk1_5_checked, root1Node51Step2Chunk2_0_checked, root1Node51Step2Chunk2_1_checked, root1Node51Step2Chunk2_2_checked, root1Node51Step2Chunk2_3_checked, root1Node51Step2Chunk2_4_checked, root1Node51Step2Chunk2_5_checked, root1Node51Step2Chunk3_0_checked, root1Node51Step2Chunk3_1_checked, root1Node51Step2Chunk3_2_checked, root1Node51Step2Chunk3_3_checked, root1Node51Step2Chunk3_4_checked, root1Node51Step2Chunk3_5_checked, root1Node51Step2Chunk4_0_checked, root1Node51Step2Chunk4_1_checked, root1Node51Step2Chunk4_2_checked, root1Node51Step2Chunk4_3_checked, root1Node51Step2Chunk4_4_checked, root1Node51Step2Chunk4_5_checked, root1Node51Step2Chunk5_0_checked, root1Node51Step2Chunk5_1_checked, root1Node51Step2Chunk5_2_checked, root1Node51Step2Chunk5_3_checked, root1Node51Step2Chunk5_4_checked, root1Node51Step2Chunk5_5_checked, root1Node51Step2Chunk6_0_checked, root1Node51Step2Chunk6_1_checked, root1Node51Step2Chunk6_2_checked, root1Node51Step2Chunk6_3_checked, root1Node51Step2Chunk6_4_checked, root1Node51Step2Chunk6_5_checked, root1Node51Step2Chunk7_0_checked, root1Node51Step2Chunk7_1_checked, root1Node51Step2Chunk7_2_checked, root1Node51Step2Chunk7_3_checked, root1Node51Step2Chunk7_4_checked, root1Node51Step2Chunk7_5_checked, root1Node51Step2Chunk8_0_checked, root1Node51Step2Chunk8_1_checked, root1Node51Step2Chunk8_2_checked, root1Node51Step2Chunk8_3_checked, root1Node51Step2Chunk8_4_checked, root1Node51Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node51Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(4,5),(8,5)]
  | 6 => [(1,0)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(0,0),(6,3)]
  | 12 => [(7,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(0,2),(1,5)]
  | 19 => [(1,1),(6,1)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(7,4)]
  | 24 => [(6,3)]
  | 25 => [(7,2)]
  | 26 => [(5,2),(5,5)]
  | 27 => [(7,0),(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(1,0)]
  | 31 => [(2,1)]
  | 32 => [(0,2)]
  | 33 => [(1,1)]
  | 34 => [(4,1),(8,1)]
  | 35 => [(4,4),(5,4),(8,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(0,0)]
  | 40 => [(3,2)]
  | 41 => [(4,0)]
  | 42 => [(5,3),(7,3),(8,3)]
  | 43 => [(7,5)]
  | 44 => [(6,0)]
  | 45 => [(7,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1)]
  | 49 => [(0,1)]
  | 50 => [(8,2)]
  | 51 => [(5,0)]
  | 52 => [(4,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(8,5)]
  | 56 => [(5,4),(8,4)]
  | 57 => [(0,0)]
  | 58 => [(7,2)]
  | 59 => [(7,4)]
  | _ => [(1,3),(6,3)]
def root1Node51Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(1,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(7,4)]
  | 24 => some [(6,3)]
  | 25 => some [(7,2)]
  | 26 => some [(5,2),(5,5)]
  | 27 => some [(7,0),(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(1,0)]
  | 31 => some [(2,1)]
  | 32 => some [(0,2)]
  | 33 => some [(1,1)]
  | 34 => some [(4,1),(8,1)]
  | 35 => some [(4,4),(5,4),(8,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(0,0)]
  | 40 => some [(3,2)]
  | 41 => some [(4,0)]
  | 42 => some [(5,3),(7,3),(8,3)]
  | 43 => some [(7,5)]
  | 44 => some [(6,0)]
  | 45 => some [(7,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(8,2)]
  | 51 => some [(5,0)]
  | 52 => some [(4,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(0,0)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(1,3),(6,3)]
theorem root1Node51Domains3_fast_eq : root1Node51Domains3 = expandDomains root1Node51Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node51Domains3 v = expandDomains root1Node51Domains3Fast v from by decide) v
theorem root1Node51Step3Chunk0_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_0⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk0_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_1⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk0_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_2⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk0_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_3⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk0_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_4⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk0_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_5⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk1_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_0⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk1_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_1⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk1_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_2⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk1_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_3⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk1_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_4⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk1_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_5⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk2_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_0⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk2_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_1⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk2_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_2⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk2_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_3⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk2_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_4⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk2_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_5⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk3_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_0⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk3_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_1⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk3_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_2⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk3_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_3⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk3_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_4⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk3_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_5⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk4_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_0⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk4_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_1⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk4_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_2⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk4_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_3⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk4_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_4⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk4_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_5⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk5_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_0⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk5_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_1⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk5_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_2⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk5_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_3⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk5_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_4⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk5_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_5⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk6_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_0⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk6_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_1⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk6_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_2⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk6_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_3⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk6_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_4⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk6_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_5⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk7_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_0⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk7_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_1⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk7_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_2⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk7_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_3⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk7_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_4⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk7_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_5⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk8_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_0⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk8_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_1⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk8_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_2⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk8_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_3⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk8_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_4⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3Chunk8_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_5⟩
      root1Node51Domains2 root1Node51Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains2 root1Node51Domains3
    root1Node51Domains2Fast root1Node51Domains3Fast
    root1Node51Domains2_fast_eq root1Node51Domains3_fast_eq (by decide)
theorem root1Node51Step3_checked :
    checkReplacement table11 root1Node51Domains2 root1Node51Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node51Step3Chunk0_0_checked, root1Node51Step3Chunk0_1_checked, root1Node51Step3Chunk0_2_checked, root1Node51Step3Chunk0_3_checked, root1Node51Step3Chunk0_4_checked, root1Node51Step3Chunk0_5_checked, root1Node51Step3Chunk1_0_checked, root1Node51Step3Chunk1_1_checked, root1Node51Step3Chunk1_2_checked, root1Node51Step3Chunk1_3_checked, root1Node51Step3Chunk1_4_checked, root1Node51Step3Chunk1_5_checked, root1Node51Step3Chunk2_0_checked, root1Node51Step3Chunk2_1_checked, root1Node51Step3Chunk2_2_checked, root1Node51Step3Chunk2_3_checked, root1Node51Step3Chunk2_4_checked, root1Node51Step3Chunk2_5_checked, root1Node51Step3Chunk3_0_checked, root1Node51Step3Chunk3_1_checked, root1Node51Step3Chunk3_2_checked, root1Node51Step3Chunk3_3_checked, root1Node51Step3Chunk3_4_checked, root1Node51Step3Chunk3_5_checked, root1Node51Step3Chunk4_0_checked, root1Node51Step3Chunk4_1_checked, root1Node51Step3Chunk4_2_checked, root1Node51Step3Chunk4_3_checked, root1Node51Step3Chunk4_4_checked, root1Node51Step3Chunk4_5_checked, root1Node51Step3Chunk5_0_checked, root1Node51Step3Chunk5_1_checked, root1Node51Step3Chunk5_2_checked, root1Node51Step3Chunk5_3_checked, root1Node51Step3Chunk5_4_checked, root1Node51Step3Chunk5_5_checked, root1Node51Step3Chunk6_0_checked, root1Node51Step3Chunk6_1_checked, root1Node51Step3Chunk6_2_checked, root1Node51Step3Chunk6_3_checked, root1Node51Step3Chunk6_4_checked, root1Node51Step3Chunk6_5_checked, root1Node51Step3Chunk7_0_checked, root1Node51Step3Chunk7_1_checked, root1Node51Step3Chunk7_2_checked, root1Node51Step3Chunk7_3_checked, root1Node51Step3Chunk7_4_checked, root1Node51Step3Chunk7_5_checked, root1Node51Step3Chunk8_0_checked, root1Node51Step3Chunk8_1_checked, root1Node51Step3Chunk8_2_checked, root1Node51Step3Chunk8_3_checked, root1Node51Step3Chunk8_4_checked, root1Node51Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node51Domains4 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(4,5),(8,5)]
  | 6 => [(1,0)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(0,0),(6,3)]
  | 12 => [(7,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(0,2),(1,5)]
  | 19 => [(1,1),(6,1)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(7,4)]
  | 24 => [(6,3)]
  | 25 => [(7,2)]
  | 26 => [(5,2),(5,5)]
  | 27 => [(7,0),(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(1,0)]
  | 31 => [(2,1)]
  | 32 => [(0,2)]
  | 33 => [(1,1)]
  | 34 => [(4,1)]
  | 35 => [(4,4),(5,4),(8,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(0,0)]
  | 40 => [(3,2)]
  | 41 => [(4,0)]
  | 42 => [(7,3)]
  | 43 => [(7,5)]
  | 44 => [(6,0)]
  | 45 => [(7,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1)]
  | 49 => [(0,1)]
  | 50 => [(8,2)]
  | 51 => [(5,0)]
  | 52 => [(4,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(8,5)]
  | 56 => [(5,4),(8,4)]
  | 57 => [(0,0)]
  | 58 => [(7,2)]
  | 59 => [(7,4)]
  | _ => [(1,3),(6,3)]
def root1Node51Domains4Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(1,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(7,4)]
  | 24 => some [(6,3)]
  | 25 => some [(7,2)]
  | 26 => some [(5,2),(5,5)]
  | 27 => some [(7,0),(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(1,0)]
  | 31 => some [(2,1)]
  | 32 => some [(0,2)]
  | 33 => some [(1,1)]
  | 34 => some [(4,1)]
  | 35 => some [(4,4),(5,4),(8,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(0,0)]
  | 40 => some [(3,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(6,0)]
  | 45 => some [(7,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(8,2)]
  | 51 => some [(5,0)]
  | 52 => some [(4,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(0,0)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(1,3),(6,3)]
theorem root1Node51Domains4_fast_eq : root1Node51Domains4 = expandDomains root1Node51Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node51Domains4 v = expandDomains root1Node51Domains4Fast v from by decide) v
theorem root1Node51Step4Chunk0_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_0⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk0_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_1⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk0_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_2⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk0_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_3⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk0_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_4⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk0_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_5⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk1_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_0⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk1_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_1⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk1_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_2⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk1_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_3⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk1_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_4⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk1_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_5⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk2_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_0⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk2_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_1⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk2_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_2⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk2_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_3⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk2_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_4⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk2_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_5⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk3_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_0⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk3_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_1⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk3_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_2⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk3_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_3⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk3_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_4⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk3_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_5⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk4_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_0⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk4_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_1⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk4_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_2⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk4_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_3⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk4_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_4⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk4_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_5⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk5_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_0⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk5_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_1⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk5_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_2⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk5_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_3⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk5_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_4⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk5_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_5⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk6_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_0⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk6_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_1⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk6_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_2⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk6_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_3⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk6_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_4⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk6_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_5⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk7_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_0⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk7_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_1⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk7_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_2⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk7_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_3⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk7_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_4⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk7_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_5⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk8_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_0⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk8_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_1⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk8_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_2⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk8_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_3⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk8_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_4⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4Chunk8_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_5⟩
      root1Node51Domains3 root1Node51Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node51Domains3 root1Node51Domains4
    root1Node51Domains3Fast root1Node51Domains4Fast
    root1Node51Domains3_fast_eq root1Node51Domains4_fast_eq (by decide)
theorem root1Node51Step4_checked :
    checkReplacement table16 root1Node51Domains3 root1Node51Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node51Step4Chunk0_0_checked, root1Node51Step4Chunk0_1_checked, root1Node51Step4Chunk0_2_checked, root1Node51Step4Chunk0_3_checked, root1Node51Step4Chunk0_4_checked, root1Node51Step4Chunk0_5_checked, root1Node51Step4Chunk1_0_checked, root1Node51Step4Chunk1_1_checked, root1Node51Step4Chunk1_2_checked, root1Node51Step4Chunk1_3_checked, root1Node51Step4Chunk1_4_checked, root1Node51Step4Chunk1_5_checked, root1Node51Step4Chunk2_0_checked, root1Node51Step4Chunk2_1_checked, root1Node51Step4Chunk2_2_checked, root1Node51Step4Chunk2_3_checked, root1Node51Step4Chunk2_4_checked, root1Node51Step4Chunk2_5_checked, root1Node51Step4Chunk3_0_checked, root1Node51Step4Chunk3_1_checked, root1Node51Step4Chunk3_2_checked, root1Node51Step4Chunk3_3_checked, root1Node51Step4Chunk3_4_checked, root1Node51Step4Chunk3_5_checked, root1Node51Step4Chunk4_0_checked, root1Node51Step4Chunk4_1_checked, root1Node51Step4Chunk4_2_checked, root1Node51Step4Chunk4_3_checked, root1Node51Step4Chunk4_4_checked, root1Node51Step4Chunk4_5_checked, root1Node51Step4Chunk5_0_checked, root1Node51Step4Chunk5_1_checked, root1Node51Step4Chunk5_2_checked, root1Node51Step4Chunk5_3_checked, root1Node51Step4Chunk5_4_checked, root1Node51Step4Chunk5_5_checked, root1Node51Step4Chunk6_0_checked, root1Node51Step4Chunk6_1_checked, root1Node51Step4Chunk6_2_checked, root1Node51Step4Chunk6_3_checked, root1Node51Step4Chunk6_4_checked, root1Node51Step4Chunk6_5_checked, root1Node51Step4Chunk7_0_checked, root1Node51Step4Chunk7_1_checked, root1Node51Step4Chunk7_2_checked, root1Node51Step4Chunk7_3_checked, root1Node51Step4Chunk7_4_checked, root1Node51Step4Chunk7_5_checked, root1Node51Step4Chunk8_0_checked, root1Node51Step4Chunk8_1_checked, root1Node51Step4Chunk8_2_checked, root1Node51Step4Chunk8_3_checked, root1Node51Step4Chunk8_4_checked, root1Node51Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node52Domains0 : Domains 61 State := restrict root1Node51Domains4 5 (4,5)
def root1Node52Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(4,5)]
  | 6 => some [(1,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(7,4)]
  | 24 => some [(6,3)]
  | 25 => some [(7,2)]
  | 26 => some [(5,2),(5,5)]
  | 27 => some [(7,0),(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(1,0)]
  | 31 => some [(2,1)]
  | 32 => some [(0,2)]
  | 33 => some [(1,1)]
  | 34 => some [(4,1)]
  | 35 => some [(4,4),(5,4),(8,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(0,0)]
  | 40 => some [(3,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(6,0)]
  | 45 => some [(7,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(8,2)]
  | 51 => some [(5,0)]
  | 52 => some [(4,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(0,0)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(1,3),(6,3)]
theorem root1Node52Domains0_fast_eq : root1Node52Domains0 = expandDomains root1Node52Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node52Domains0 v = expandDomains root1Node52Domains0Fast v from by decide) v
def root1Node52Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(4,5)]
  | 6 => [(1,0)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(7,4)]
  | 24 => [(6,3)]
  | 25 => [(7,2)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(1,0)]
  | 31 => [(2,1)]
  | 32 => [(0,2)]
  | 33 => [(1,1)]
  | 34 => [(4,1)]
  | 35 => [(4,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(0,0)]
  | 40 => [(3,2)]
  | 41 => [(4,0)]
  | 42 => [(7,3)]
  | 43 => [(7,5)]
  | 44 => [(6,0)]
  | 45 => [(7,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1)]
  | 49 => [(0,1)]
  | 50 => [(8,2)]
  | 51 => [(5,0)]
  | 52 => [(4,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(8,5)]
  | 56 => [(5,4),(8,4)]
  | 57 => [(0,0)]
  | 58 => [(7,2)]
  | 59 => [(7,4)]
  | _ => [(1,3),(6,3)]
def root1Node52Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(4,5)]
  | 6 => some [(1,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(7,4)]
  | 24 => some [(6,3)]
  | 25 => some [(7,2)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(1,0)]
  | 31 => some [(2,1)]
  | 32 => some [(0,2)]
  | 33 => some [(1,1)]
  | 34 => some [(4,1)]
  | 35 => some [(4,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(0,0)]
  | 40 => some [(3,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(6,0)]
  | 45 => some [(7,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(8,2)]
  | 51 => some [(5,0)]
  | 52 => some [(4,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(0,0)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(1,3),(6,3)]
theorem root1Node52Domains1_fast_eq : root1Node52Domains1 = expandDomains root1Node52Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node52Domains1 v = expandDomains root1Node52Domains1Fast v from by decide) v
theorem root1Node52Step1Chunk0_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_0⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk0_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_1⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk0_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_2⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk0_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_3⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk0_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_4⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk0_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_5⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk1_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_0⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk1_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_1⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk1_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_2⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk1_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_3⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk1_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_4⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk1_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_5⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk2_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_0⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk2_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_1⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk2_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_2⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk2_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_3⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk2_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_4⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk2_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_5⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk3_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_0⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk3_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_1⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk3_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_2⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk3_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_3⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk3_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_4⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk3_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_5⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk4_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_0⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk4_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_1⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk4_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_2⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk4_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_3⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk4_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_4⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk4_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_5⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk5_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_0⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk5_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_1⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk5_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_2⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk5_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_3⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk5_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_4⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk5_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_5⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk6_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_0⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk6_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_1⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk6_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_2⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk6_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_3⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk6_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_4⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk6_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_5⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk7_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_0⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk7_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_1⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk7_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_2⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk7_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_3⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk7_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_4⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk7_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_5⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk8_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_0⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk8_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_1⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk8_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_2⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk8_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_3⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk8_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_4⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1Chunk8_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_5⟩
      root1Node52Domains0 root1Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains0 root1Node52Domains1
    root1Node52Domains0Fast root1Node52Domains1Fast
    root1Node52Domains0_fast_eq root1Node52Domains1_fast_eq (by decide)
theorem root1Node52Step1_checked :
    checkReplacement table11 root1Node52Domains0 root1Node52Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node52Step1Chunk0_0_checked, root1Node52Step1Chunk0_1_checked, root1Node52Step1Chunk0_2_checked, root1Node52Step1Chunk0_3_checked, root1Node52Step1Chunk0_4_checked, root1Node52Step1Chunk0_5_checked, root1Node52Step1Chunk1_0_checked, root1Node52Step1Chunk1_1_checked, root1Node52Step1Chunk1_2_checked, root1Node52Step1Chunk1_3_checked, root1Node52Step1Chunk1_4_checked, root1Node52Step1Chunk1_5_checked, root1Node52Step1Chunk2_0_checked, root1Node52Step1Chunk2_1_checked, root1Node52Step1Chunk2_2_checked, root1Node52Step1Chunk2_3_checked, root1Node52Step1Chunk2_4_checked, root1Node52Step1Chunk2_5_checked, root1Node52Step1Chunk3_0_checked, root1Node52Step1Chunk3_1_checked, root1Node52Step1Chunk3_2_checked, root1Node52Step1Chunk3_3_checked, root1Node52Step1Chunk3_4_checked, root1Node52Step1Chunk3_5_checked, root1Node52Step1Chunk4_0_checked, root1Node52Step1Chunk4_1_checked, root1Node52Step1Chunk4_2_checked, root1Node52Step1Chunk4_3_checked, root1Node52Step1Chunk4_4_checked, root1Node52Step1Chunk4_5_checked, root1Node52Step1Chunk5_0_checked, root1Node52Step1Chunk5_1_checked, root1Node52Step1Chunk5_2_checked, root1Node52Step1Chunk5_3_checked, root1Node52Step1Chunk5_4_checked, root1Node52Step1Chunk5_5_checked, root1Node52Step1Chunk6_0_checked, root1Node52Step1Chunk6_1_checked, root1Node52Step1Chunk6_2_checked, root1Node52Step1Chunk6_3_checked, root1Node52Step1Chunk6_4_checked, root1Node52Step1Chunk6_5_checked, root1Node52Step1Chunk7_0_checked, root1Node52Step1Chunk7_1_checked, root1Node52Step1Chunk7_2_checked, root1Node52Step1Chunk7_3_checked, root1Node52Step1Chunk7_4_checked, root1Node52Step1Chunk7_5_checked, root1Node52Step1Chunk8_0_checked, root1Node52Step1Chunk8_1_checked, root1Node52Step1Chunk8_2_checked, root1Node52Step1Chunk8_3_checked, root1Node52Step1Chunk8_4_checked, root1Node52Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node52Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(4,5)]
  | 6 => [(1,0)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(0,3)]
  | 10 => [(8,1)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(7,4)]
  | 24 => [(6,3)]
  | 25 => [(7,2)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(1,0)]
  | 31 => [(2,1)]
  | 32 => [(0,2)]
  | 33 => [(1,1)]
  | 34 => [(4,1)]
  | 35 => [(4,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(0,0)]
  | 40 => [(3,2)]
  | 41 => [(4,0)]
  | 42 => [(7,3)]
  | 43 => [(7,5)]
  | 44 => [(6,0)]
  | 45 => [(7,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1)]
  | 49 => [(0,1)]
  | 50 => [(8,2)]
  | 51 => [(5,0)]
  | 52 => [(4,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(8,5)]
  | 56 => [(8,4)]
  | 57 => [(0,0)]
  | 58 => [(7,2)]
  | 59 => [(7,4)]
  | _ => [(1,3),(6,3)]
def root1Node52Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(4,5)]
  | 6 => some [(1,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(7,4)]
  | 24 => some [(6,3)]
  | 25 => some [(7,2)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(1,0)]
  | 31 => some [(2,1)]
  | 32 => some [(0,2)]
  | 33 => some [(1,1)]
  | 34 => some [(4,1)]
  | 35 => some [(4,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(0,0)]
  | 40 => some [(3,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(6,0)]
  | 45 => some [(7,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(8,2)]
  | 51 => some [(5,0)]
  | 52 => some [(4,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => some [(8,4)]
  | 57 => some [(0,0)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(1,3),(6,3)]
theorem root1Node52Domains2_fast_eq : root1Node52Domains2 = expandDomains root1Node52Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node52Domains2 v = expandDomains root1Node52Domains2Fast v from by decide) v
theorem root1Node52Step2Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root1Node52Domains1 root1Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node52Domains1 root1Node52Domains2
    root1Node52Domains1Fast root1Node52Domains2Fast
    root1Node52Domains1_fast_eq root1Node52Domains2_fast_eq (by decide)
theorem root1Node52Step2_checked :
    checkReplacement table35 root1Node52Domains1 root1Node52Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node52Step2Chunk0_0_checked, root1Node52Step2Chunk0_1_checked, root1Node52Step2Chunk0_2_checked, root1Node52Step2Chunk0_3_checked, root1Node52Step2Chunk0_4_checked, root1Node52Step2Chunk0_5_checked, root1Node52Step2Chunk1_0_checked, root1Node52Step2Chunk1_1_checked, root1Node52Step2Chunk1_2_checked, root1Node52Step2Chunk1_3_checked, root1Node52Step2Chunk1_4_checked, root1Node52Step2Chunk1_5_checked, root1Node52Step2Chunk2_0_checked, root1Node52Step2Chunk2_1_checked, root1Node52Step2Chunk2_2_checked, root1Node52Step2Chunk2_3_checked, root1Node52Step2Chunk2_4_checked, root1Node52Step2Chunk2_5_checked, root1Node52Step2Chunk3_0_checked, root1Node52Step2Chunk3_1_checked, root1Node52Step2Chunk3_2_checked, root1Node52Step2Chunk3_3_checked, root1Node52Step2Chunk3_4_checked, root1Node52Step2Chunk3_5_checked, root1Node52Step2Chunk4_0_checked, root1Node52Step2Chunk4_1_checked, root1Node52Step2Chunk4_2_checked, root1Node52Step2Chunk4_3_checked, root1Node52Step2Chunk4_4_checked, root1Node52Step2Chunk4_5_checked, root1Node52Step2Chunk5_0_checked, root1Node52Step2Chunk5_1_checked, root1Node52Step2Chunk5_2_checked, root1Node52Step2Chunk5_3_checked, root1Node52Step2Chunk5_4_checked, root1Node52Step2Chunk5_5_checked, root1Node52Step2Chunk6_0_checked, root1Node52Step2Chunk6_1_checked, root1Node52Step2Chunk6_2_checked, root1Node52Step2Chunk6_3_checked, root1Node52Step2Chunk6_4_checked, root1Node52Step2Chunk6_5_checked, root1Node52Step2Chunk7_0_checked, root1Node52Step2Chunk7_1_checked, root1Node52Step2Chunk7_2_checked, root1Node52Step2Chunk7_3_checked, root1Node52Step2Chunk7_4_checked, root1Node52Step2Chunk7_5_checked, root1Node52Step2Chunk8_0_checked, root1Node52Step2Chunk8_1_checked, root1Node52Step2Chunk8_2_checked, root1Node52Step2Chunk8_3_checked, root1Node52Step2Chunk8_4_checked, root1Node52Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
