module

public import SpectreFinite.RadiusFourRoot6Part13
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable23
public import SpectreFinite.RadiusFourTable35
public import SpectreFinite.RadiusFourTable37
public import SpectreFinite.RadiusFourTable39
public import SpectreFinite.RadiusFourTable4

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node47Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,1)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(8,1)]
  | 9 => [(6,5)]
  | 10 => [(0,4)]
  | 11 => [(1,3),(3,3),(7,3)]
  | 12 => [(5,2)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(7,0)]
  | 17 => [(2,3),(2,5),(4,3)]
  | 18 => [(0,1),(6,5)]
  | 19 => [(0,4),(6,2)]
  | 20 => [(5,4),(8,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4),(6,4)]
  | 25 => [(0,5),(1,2),(7,2)]
  | 26 => [(4,5)]
  | 27 => [(1,0),(7,0)]
  | 28 => [(4,3),(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(0,3),(6,0)]
  | 34 => [(3,1),(5,1),(7,1)]
  | 35 => [(7,2)]
  | 36 => [(4,0),(7,4)]
  | 37 => [(1,3),(7,3)]
  | 38 => [(8,2)]
  | 39 => [(8,0)]
  | 40 => [(7,3)]
  | 41 => [(4,2),(8,2)]
  | 42 => [(5,0),(5,3)]
  | 43 => [(5,1),(8,1)]
  | 44 => [(0,1),(6,5)]
  | 45 => [(0,4),(6,2)]
  | 46 => [(5,4),(8,4)]
  | 47 => [(6,4)]
  | 48 => [(1,2)]
  | 49 => [(7,4),(8,4)]
  | 50 => [(5,5),(8,5)]
  | 51 => [(1,0),(7,0)]
  | 52 => [(4,3),(7,1)]
  | 53 => [(3,5),(7,5)]
  | 54 => [(0,3)]
  | 55 => [(4,1),(8,1)]
  | 56 => [(4,4),(7,2),(8,2)]
  | 57 => [(1,4),(4,0),(7,4),(8,0)]
  | 58 => [(0,5),(1,3),(6,3),(7,3)]
  | 59 => [(2,2),(2,4),(4,2)]
  | _ => [(1,3),(3,3),(5,3)]
def root6Node47Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(1,3),(3,3),(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(2,3),(2,5),(4,3)]
  | 18 => some [(0,1),(6,5)]
  | 19 => some [(0,4),(6,2)]
  | 20 => some [(5,4),(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(7,2)]
  | 26 => some [(4,5)]
  | 27 => some [(1,0),(7,0)]
  | 28 => some [(4,3),(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3),(6,0)]
  | 34 => some [(3,1),(5,1),(7,1)]
  | 35 => some [(7,2)]
  | 36 => some [(4,0),(7,4)]
  | 37 => some [(1,3),(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2),(8,2)]
  | 42 => some [(5,0),(5,3)]
  | 43 => some [(5,1),(8,1)]
  | 44 => some [(0,1),(6,5)]
  | 45 => some [(0,4),(6,2)]
  | 46 => some [(5,4),(8,4)]
  | 47 => some [(6,4)]
  | 48 => some [(1,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(5,5),(8,5)]
  | 51 => some [(1,0),(7,0)]
  | 52 => some [(4,3),(7,1)]
  | 53 => some [(3,5),(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(4,1),(8,1)]
  | 56 => some [(4,4),(7,2),(8,2)]
  | 57 => some [(1,4),(4,0),(7,4),(8,0)]
  | 58 => some [(0,5),(1,3),(6,3),(7,3)]
  | 59 => some [(2,2),(2,4),(4,2)]
  | _ => some [(1,3),(3,3),(5,3)]
theorem root6Node47Domains2_fast_eq : root6Node47Domains2 = expandDomains root6Node47Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node47Domains2 v = expandDomains root6Node47Domains2Fast v from by decide) v
theorem root6Node47Step2Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root6Node47Domains1 root6Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains1 root6Node47Domains2
    root6Node47Domains1Fast root6Node47Domains2Fast
    root6Node47Domains1_fast_eq root6Node47Domains2_fast_eq (by decide)
theorem root6Node47Step2_checked :
    checkReplacement table35 root6Node47Domains1 root6Node47Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node47Step2Chunk0_0_checked, root6Node47Step2Chunk0_1_checked, root6Node47Step2Chunk0_2_checked, root6Node47Step2Chunk0_3_checked, root6Node47Step2Chunk0_4_checked, root6Node47Step2Chunk0_5_checked, root6Node47Step2Chunk1_0_checked, root6Node47Step2Chunk1_1_checked, root6Node47Step2Chunk1_2_checked, root6Node47Step2Chunk1_3_checked, root6Node47Step2Chunk1_4_checked, root6Node47Step2Chunk1_5_checked, root6Node47Step2Chunk2_0_checked, root6Node47Step2Chunk2_1_checked, root6Node47Step2Chunk2_2_checked, root6Node47Step2Chunk2_3_checked, root6Node47Step2Chunk2_4_checked, root6Node47Step2Chunk2_5_checked, root6Node47Step2Chunk3_0_checked, root6Node47Step2Chunk3_1_checked, root6Node47Step2Chunk3_2_checked, root6Node47Step2Chunk3_3_checked, root6Node47Step2Chunk3_4_checked, root6Node47Step2Chunk3_5_checked, root6Node47Step2Chunk4_0_checked, root6Node47Step2Chunk4_1_checked, root6Node47Step2Chunk4_2_checked, root6Node47Step2Chunk4_3_checked, root6Node47Step2Chunk4_4_checked, root6Node47Step2Chunk4_5_checked, root6Node47Step2Chunk5_0_checked, root6Node47Step2Chunk5_1_checked, root6Node47Step2Chunk5_2_checked, root6Node47Step2Chunk5_3_checked, root6Node47Step2Chunk5_4_checked, root6Node47Step2Chunk5_5_checked, root6Node47Step2Chunk6_0_checked, root6Node47Step2Chunk6_1_checked, root6Node47Step2Chunk6_2_checked, root6Node47Step2Chunk6_3_checked, root6Node47Step2Chunk6_4_checked, root6Node47Step2Chunk6_5_checked, root6Node47Step2Chunk7_0_checked, root6Node47Step2Chunk7_1_checked, root6Node47Step2Chunk7_2_checked, root6Node47Step2Chunk7_3_checked, root6Node47Step2Chunk7_4_checked, root6Node47Step2Chunk7_5_checked, root6Node47Step2Chunk8_0_checked, root6Node47Step2Chunk8_1_checked, root6Node47Step2Chunk8_2_checked, root6Node47Step2Chunk8_3_checked, root6Node47Step2Chunk8_4_checked, root6Node47Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node47Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,1)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(8,1)]
  | 9 => [(6,5)]
  | 10 => [(0,4)]
  | 11 => [(1,3),(3,3),(7,3)]
  | 12 => [(5,2)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(7,0)]
  | 17 => [(2,3),(4,3)]
  | 18 => [(0,1),(6,5)]
  | 19 => [(0,4),(6,2)]
  | 20 => [(5,4),(8,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4),(6,4)]
  | 25 => [(0,5),(1,2)]
  | 26 => [(4,5)]
  | 27 => [(1,0),(7,0)]
  | 28 => [(4,3),(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(0,3),(6,0)]
  | 34 => [(3,1),(5,1),(7,1)]
  | 35 => [(7,2)]
  | 36 => [(4,0),(7,4)]
  | 37 => [(1,3),(7,3)]
  | 38 => [(8,2)]
  | 39 => [(8,0)]
  | 40 => [(7,3)]
  | 41 => [(4,2),(8,2)]
  | 42 => [(5,0),(5,3)]
  | 43 => [(5,1),(8,1)]
  | 44 => [(0,1),(6,5)]
  | 45 => [(0,4),(6,2)]
  | 46 => [(5,4),(8,4)]
  | 47 => [(6,4)]
  | 48 => [(1,2)]
  | 49 => [(7,4),(8,4)]
  | 50 => [(5,5),(8,5)]
  | 51 => [(1,0),(7,0)]
  | 52 => [(4,3),(7,1)]
  | 53 => [(3,5),(7,5)]
  | 54 => [(0,3)]
  | 55 => [(4,1),(8,1)]
  | 56 => [(4,4),(7,2),(8,2)]
  | 57 => [(1,4),(4,0),(7,4),(8,0)]
  | 58 => [(0,5),(1,3),(6,3),(7,3)]
  | 59 => [(2,2),(2,4),(4,2)]
  | _ => [(1,3),(3,3),(5,3)]
def root6Node47Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(1,3),(3,3),(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(2,3),(4,3)]
  | 18 => some [(0,1),(6,5)]
  | 19 => some [(0,4),(6,2)]
  | 20 => some [(5,4),(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4),(6,4)]
  | 25 => some [(0,5),(1,2)]
  | 26 => some [(4,5)]
  | 27 => some [(1,0),(7,0)]
  | 28 => some [(4,3),(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3),(6,0)]
  | 34 => some [(3,1),(5,1),(7,1)]
  | 35 => some [(7,2)]
  | 36 => some [(4,0),(7,4)]
  | 37 => some [(1,3),(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2),(8,2)]
  | 42 => some [(5,0),(5,3)]
  | 43 => some [(5,1),(8,1)]
  | 44 => some [(0,1),(6,5)]
  | 45 => some [(0,4),(6,2)]
  | 46 => some [(5,4),(8,4)]
  | 47 => some [(6,4)]
  | 48 => some [(1,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(5,5),(8,5)]
  | 51 => some [(1,0),(7,0)]
  | 52 => some [(4,3),(7,1)]
  | 53 => some [(3,5),(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(4,1),(8,1)]
  | 56 => some [(4,4),(7,2),(8,2)]
  | 57 => some [(1,4),(4,0),(7,4),(8,0)]
  | 58 => some [(0,5),(1,3),(6,3),(7,3)]
  | 59 => some [(2,2),(2,4),(4,2)]
  | _ => some [(1,3),(3,3),(5,3)]
theorem root6Node47Domains3_fast_eq : root6Node47Domains3 = expandDomains root6Node47Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node47Domains3 v = expandDomains root6Node47Domains3Fast v from by decide) v
theorem root6Node47Step3Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root6Node47Domains2 root6Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node47Domains2 root6Node47Domains3
    root6Node47Domains2Fast root6Node47Domains3Fast
    root6Node47Domains2_fast_eq root6Node47Domains3_fast_eq (by decide)
theorem root6Node47Step3_checked :
    checkReplacement table4 root6Node47Domains2 root6Node47Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node47Step3Chunk0_0_checked, root6Node47Step3Chunk0_1_checked, root6Node47Step3Chunk0_2_checked, root6Node47Step3Chunk0_3_checked, root6Node47Step3Chunk0_4_checked, root6Node47Step3Chunk0_5_checked, root6Node47Step3Chunk1_0_checked, root6Node47Step3Chunk1_1_checked, root6Node47Step3Chunk1_2_checked, root6Node47Step3Chunk1_3_checked, root6Node47Step3Chunk1_4_checked, root6Node47Step3Chunk1_5_checked, root6Node47Step3Chunk2_0_checked, root6Node47Step3Chunk2_1_checked, root6Node47Step3Chunk2_2_checked, root6Node47Step3Chunk2_3_checked, root6Node47Step3Chunk2_4_checked, root6Node47Step3Chunk2_5_checked, root6Node47Step3Chunk3_0_checked, root6Node47Step3Chunk3_1_checked, root6Node47Step3Chunk3_2_checked, root6Node47Step3Chunk3_3_checked, root6Node47Step3Chunk3_4_checked, root6Node47Step3Chunk3_5_checked, root6Node47Step3Chunk4_0_checked, root6Node47Step3Chunk4_1_checked, root6Node47Step3Chunk4_2_checked, root6Node47Step3Chunk4_3_checked, root6Node47Step3Chunk4_4_checked, root6Node47Step3Chunk4_5_checked, root6Node47Step3Chunk5_0_checked, root6Node47Step3Chunk5_1_checked, root6Node47Step3Chunk5_2_checked, root6Node47Step3Chunk5_3_checked, root6Node47Step3Chunk5_4_checked, root6Node47Step3Chunk5_5_checked, root6Node47Step3Chunk6_0_checked, root6Node47Step3Chunk6_1_checked, root6Node47Step3Chunk6_2_checked, root6Node47Step3Chunk6_3_checked, root6Node47Step3Chunk6_4_checked, root6Node47Step3Chunk6_5_checked, root6Node47Step3Chunk7_0_checked, root6Node47Step3Chunk7_1_checked, root6Node47Step3Chunk7_2_checked, root6Node47Step3Chunk7_3_checked, root6Node47Step3Chunk7_4_checked, root6Node47Step3Chunk7_5_checked, root6Node47Step3Chunk8_0_checked, root6Node47Step3Chunk8_1_checked, root6Node47Step3Chunk8_2_checked, root6Node47Step3Chunk8_3_checked, root6Node47Step3Chunk8_4_checked, root6Node47Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node48Domains0 : Domains 61 State := restrict root6Node47Domains3 17 (2,3)
def root6Node48Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(1,3),(3,3),(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(2,3)]
  | 18 => some [(0,1),(6,5)]
  | 19 => some [(0,4),(6,2)]
  | 20 => some [(5,4),(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4),(6,4)]
  | 25 => some [(0,5),(1,2)]
  | 26 => some [(4,5)]
  | 27 => some [(1,0),(7,0)]
  | 28 => some [(4,3),(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3),(6,0)]
  | 34 => some [(3,1),(5,1),(7,1)]
  | 35 => some [(7,2)]
  | 36 => some [(4,0),(7,4)]
  | 37 => some [(1,3),(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2),(8,2)]
  | 42 => some [(5,0),(5,3)]
  | 43 => some [(5,1),(8,1)]
  | 44 => some [(0,1),(6,5)]
  | 45 => some [(0,4),(6,2)]
  | 46 => some [(5,4),(8,4)]
  | 47 => some [(6,4)]
  | 48 => some [(1,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(5,5),(8,5)]
  | 51 => some [(1,0),(7,0)]
  | 52 => some [(4,3),(7,1)]
  | 53 => some [(3,5),(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(4,1),(8,1)]
  | 56 => some [(4,4),(7,2),(8,2)]
  | 57 => some [(1,4),(4,0),(7,4),(8,0)]
  | 58 => some [(0,5),(1,3),(6,3),(7,3)]
  | 59 => some [(2,2),(2,4),(4,2)]
  | _ => some [(1,3),(3,3),(5,3)]
theorem root6Node48Domains0_fast_eq : root6Node48Domains0 = expandDomains root6Node48Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node48Domains0 v = expandDomains root6Node48Domains0Fast v from by decide) v
def root6Node48Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,1)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(8,1)]
  | 9 => [(6,5)]
  | 10 => [(0,4)]
  | 11 => [(1,3),(3,3),(7,3)]
  | 12 => [(5,2)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(7,0)]
  | 17 => [(2,3)]
  | 18 => [(0,1),(6,5)]
  | 19 => [(0,4),(6,2)]
  | 20 => [(5,4),(8,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(4,5)]
  | 27 => [(1,0),(7,0)]
  | 28 => [(4,3),(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(0,3)]
  | 34 => [(5,1)]
  | 35 => [(7,2)]
  | 36 => [(4,0),(7,4)]
  | 37 => [(1,3),(7,3)]
  | 38 => [(8,2)]
  | 39 => [(8,0)]
  | 40 => [(7,3)]
  | 41 => [(4,2)]
  | 42 => [(5,3)]
  | 43 => [(5,1),(8,1)]
  | 44 => [(0,1),(6,5)]
  | 45 => [(0,4),(6,2)]
  | 46 => [(5,4),(8,4)]
  | 47 => [(6,4)]
  | 48 => [(1,2)]
  | 49 => [(7,4)]
  | 50 => [(5,5),(8,5)]
  | 51 => [(1,0),(7,0)]
  | 52 => [(4,3),(7,1)]
  | 53 => [(3,5),(7,5)]
  | 54 => [(0,3)]
  | 55 => [(4,1),(8,1)]
  | 56 => [(4,4),(7,2),(8,2)]
  | 57 => [(1,4),(4,0),(7,4),(8,0)]
  | 58 => [(0,5),(1,3),(6,3),(7,3)]
  | 59 => [(2,2),(2,4),(4,2)]
  | _ => [(1,3),(3,3),(5,3)]
def root6Node48Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(1,3),(3,3),(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(2,3)]
  | 18 => some [(0,1),(6,5)]
  | 19 => some [(0,4),(6,2)]
  | 20 => some [(5,4),(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(4,5)]
  | 27 => some [(1,0),(7,0)]
  | 28 => some [(4,3),(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2)]
  | 36 => some [(4,0),(7,4)]
  | 37 => some [(1,3),(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(5,1),(8,1)]
  | 44 => some [(0,1),(6,5)]
  | 45 => some [(0,4),(6,2)]
  | 46 => some [(5,4),(8,4)]
  | 47 => some [(6,4)]
  | 48 => some [(1,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,5),(8,5)]
  | 51 => some [(1,0),(7,0)]
  | 52 => some [(4,3),(7,1)]
  | 53 => some [(3,5),(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(4,1),(8,1)]
  | 56 => some [(4,4),(7,2),(8,2)]
  | 57 => some [(1,4),(4,0),(7,4),(8,0)]
  | 58 => some [(0,5),(1,3),(6,3),(7,3)]
  | 59 => some [(2,2),(2,4),(4,2)]
  | _ => some [(1,3),(3,3),(5,3)]
theorem root6Node48Domains1_fast_eq : root6Node48Domains1 = expandDomains root6Node48Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node48Domains1 v = expandDomains root6Node48Domains1Fast v from by decide) v
theorem root6Node48Step1Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root6Node48Domains0 root6Node48Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node48Domains0 root6Node48Domains1
    root6Node48Domains0Fast root6Node48Domains1Fast
    root6Node48Domains0_fast_eq root6Node48Domains1_fast_eq (by decide)
theorem root6Node48Step1_checked :
    checkReplacement table23 root6Node48Domains0 root6Node48Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node48Step1Chunk0_0_checked, root6Node48Step1Chunk0_1_checked, root6Node48Step1Chunk0_2_checked, root6Node48Step1Chunk0_3_checked, root6Node48Step1Chunk0_4_checked, root6Node48Step1Chunk0_5_checked, root6Node48Step1Chunk1_0_checked, root6Node48Step1Chunk1_1_checked, root6Node48Step1Chunk1_2_checked, root6Node48Step1Chunk1_3_checked, root6Node48Step1Chunk1_4_checked, root6Node48Step1Chunk1_5_checked, root6Node48Step1Chunk2_0_checked, root6Node48Step1Chunk2_1_checked, root6Node48Step1Chunk2_2_checked, root6Node48Step1Chunk2_3_checked, root6Node48Step1Chunk2_4_checked, root6Node48Step1Chunk2_5_checked, root6Node48Step1Chunk3_0_checked, root6Node48Step1Chunk3_1_checked, root6Node48Step1Chunk3_2_checked, root6Node48Step1Chunk3_3_checked, root6Node48Step1Chunk3_4_checked, root6Node48Step1Chunk3_5_checked, root6Node48Step1Chunk4_0_checked, root6Node48Step1Chunk4_1_checked, root6Node48Step1Chunk4_2_checked, root6Node48Step1Chunk4_3_checked, root6Node48Step1Chunk4_4_checked, root6Node48Step1Chunk4_5_checked, root6Node48Step1Chunk5_0_checked, root6Node48Step1Chunk5_1_checked, root6Node48Step1Chunk5_2_checked, root6Node48Step1Chunk5_3_checked, root6Node48Step1Chunk5_4_checked, root6Node48Step1Chunk5_5_checked, root6Node48Step1Chunk6_0_checked, root6Node48Step1Chunk6_1_checked, root6Node48Step1Chunk6_2_checked, root6Node48Step1Chunk6_3_checked, root6Node48Step1Chunk6_4_checked, root6Node48Step1Chunk6_5_checked, root6Node48Step1Chunk7_0_checked, root6Node48Step1Chunk7_1_checked, root6Node48Step1Chunk7_2_checked, root6Node48Step1Chunk7_3_checked, root6Node48Step1Chunk7_4_checked, root6Node48Step1Chunk7_5_checked, root6Node48Step1Chunk8_0_checked, root6Node48Step1Chunk8_1_checked, root6Node48Step1Chunk8_2_checked, root6Node48Step1Chunk8_3_checked, root6Node48Step1Chunk8_4_checked, root6Node48Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node49Domains0 : Domains 61 State := restrict root6Node48Domains1 18 (0,1)
def root6Node49Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(1,3),(3,3),(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(2,3)]
  | 18 => some [(0,1)]
  | 19 => some [(0,4),(6,2)]
  | 20 => some [(5,4),(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(4,5)]
  | 27 => some [(1,0),(7,0)]
  | 28 => some [(4,3),(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2)]
  | 36 => some [(4,0),(7,4)]
  | 37 => some [(1,3),(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(5,1),(8,1)]
  | 44 => some [(0,1),(6,5)]
  | 45 => some [(0,4),(6,2)]
  | 46 => some [(5,4),(8,4)]
  | 47 => some [(6,4)]
  | 48 => some [(1,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,5),(8,5)]
  | 51 => some [(1,0),(7,0)]
  | 52 => some [(4,3),(7,1)]
  | 53 => some [(3,5),(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(4,1),(8,1)]
  | 56 => some [(4,4),(7,2),(8,2)]
  | 57 => some [(1,4),(4,0),(7,4),(8,0)]
  | 58 => some [(0,5),(1,3),(6,3),(7,3)]
  | 59 => some [(2,2),(2,4),(4,2)]
  | _ => some [(1,3),(3,3),(5,3)]
theorem root6Node49Domains0_fast_eq : root6Node49Domains0 = expandDomains root6Node49Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node49Domains0 v = expandDomains root6Node49Domains0Fast v from by decide) v
def root6Node49Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,1)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(8,1)]
  | 9 => [(6,5)]
  | 10 => [(0,4)]
  | 11 => [(3,3),(7,3)]
  | 12 => [(5,2)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(7,0)]
  | 17 => [(2,3)]
  | 18 => [(0,1)]
  | 19 => [(6,2)]
  | 20 => [(8,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(4,5)]
  | 27 => [(1,0)]
  | 28 => [(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(0,3)]
  | 34 => [(5,1)]
  | 35 => [(7,2)]
  | 36 => [(4,0)]
  | 37 => [(7,3)]
  | 38 => [(8,2)]
  | 39 => [(8,0)]
  | 40 => [(7,3)]
  | 41 => [(4,2)]
  | 42 => [(5,3)]
  | 43 => [(5,1)]
  | 44 => [(0,1)]
  | 45 => [(6,2)]
  | 46 => [(8,4)]
  | 47 => [(6,4)]
  | 48 => [(1,2)]
  | 49 => [(7,4)]
  | 50 => [(8,5)]
  | 51 => [(1,0)]
  | 52 => [(7,1)]
  | 53 => [(7,5)]
  | 54 => [(0,3)]
  | 55 => [(4,1),(8,1)]
  | 56 => [(7,2),(8,2)]
  | 57 => [(4,0),(8,0)]
  | 58 => [(7,3)]
  | 59 => [(2,2),(2,4),(4,2)]
  | _ => [(1,3),(3,3),(5,3)]
def root6Node49Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(3,3),(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(2,3)]
  | 18 => some [(0,1)]
  | 19 => some [(6,2)]
  | 20 => some [(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(4,5)]
  | 27 => some [(1,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2)]
  | 36 => some [(4,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(5,1)]
  | 44 => some [(0,1)]
  | 45 => some [(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(6,4)]
  | 48 => some [(1,2)]
  | 49 => some [(7,4)]
  | 50 => some [(8,5)]
  | 51 => some [(1,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(4,1),(8,1)]
  | 56 => some [(7,2),(8,2)]
  | 57 => some [(4,0),(8,0)]
  | 58 => some [(7,3)]
  | 59 => some [(2,2),(2,4),(4,2)]
  | _ => some [(1,3),(3,3),(5,3)]
theorem root6Node49Domains1_fast_eq : root6Node49Domains1 = expandDomains root6Node49Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node49Domains1 v = expandDomains root6Node49Domains1Fast v from by decide) v
theorem root6Node49Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root6Node49Domains0 root6Node49Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains0 root6Node49Domains1
    root6Node49Domains0Fast root6Node49Domains1Fast
    root6Node49Domains0_fast_eq root6Node49Domains1_fast_eq (by decide)
theorem root6Node49Step1_checked :
    checkReplacement table37 root6Node49Domains0 root6Node49Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node49Step1Chunk0_0_checked, root6Node49Step1Chunk0_1_checked, root6Node49Step1Chunk0_2_checked, root6Node49Step1Chunk0_3_checked, root6Node49Step1Chunk0_4_checked, root6Node49Step1Chunk0_5_checked, root6Node49Step1Chunk1_0_checked, root6Node49Step1Chunk1_1_checked, root6Node49Step1Chunk1_2_checked, root6Node49Step1Chunk1_3_checked, root6Node49Step1Chunk1_4_checked, root6Node49Step1Chunk1_5_checked, root6Node49Step1Chunk2_0_checked, root6Node49Step1Chunk2_1_checked, root6Node49Step1Chunk2_2_checked, root6Node49Step1Chunk2_3_checked, root6Node49Step1Chunk2_4_checked, root6Node49Step1Chunk2_5_checked, root6Node49Step1Chunk3_0_checked, root6Node49Step1Chunk3_1_checked, root6Node49Step1Chunk3_2_checked, root6Node49Step1Chunk3_3_checked, root6Node49Step1Chunk3_4_checked, root6Node49Step1Chunk3_5_checked, root6Node49Step1Chunk4_0_checked, root6Node49Step1Chunk4_1_checked, root6Node49Step1Chunk4_2_checked, root6Node49Step1Chunk4_3_checked, root6Node49Step1Chunk4_4_checked, root6Node49Step1Chunk4_5_checked, root6Node49Step1Chunk5_0_checked, root6Node49Step1Chunk5_1_checked, root6Node49Step1Chunk5_2_checked, root6Node49Step1Chunk5_3_checked, root6Node49Step1Chunk5_4_checked, root6Node49Step1Chunk5_5_checked, root6Node49Step1Chunk6_0_checked, root6Node49Step1Chunk6_1_checked, root6Node49Step1Chunk6_2_checked, root6Node49Step1Chunk6_3_checked, root6Node49Step1Chunk6_4_checked, root6Node49Step1Chunk6_5_checked, root6Node49Step1Chunk7_0_checked, root6Node49Step1Chunk7_1_checked, root6Node49Step1Chunk7_2_checked, root6Node49Step1Chunk7_3_checked, root6Node49Step1Chunk7_4_checked, root6Node49Step1Chunk7_5_checked, root6Node49Step1Chunk8_0_checked, root6Node49Step1Chunk8_1_checked, root6Node49Step1Chunk8_2_checked, root6Node49Step1Chunk8_3_checked, root6Node49Step1Chunk8_4_checked, root6Node49Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node49Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,1)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(8,1)]
  | 9 => [(6,5)]
  | 10 => [(0,4)]
  | 11 => [(3,3),(7,3)]
  | 12 => [(5,2)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(7,0)]
  | 17 => [(2,3)]
  | 18 => [(0,1)]
  | 19 => [(6,2)]
  | 20 => [(8,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(4,5)]
  | 27 => [(1,0)]
  | 28 => [(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(0,3)]
  | 34 => [(5,1)]
  | 35 => [(7,2)]
  | 36 => [(4,0)]
  | 37 => [(7,3)]
  | 38 => [(8,2)]
  | 39 => [(8,0)]
  | 40 => [(7,3)]
  | 41 => [(4,2)]
  | 42 => [(5,3)]
  | 43 => [(5,1)]
  | 44 => [(0,1)]
  | 45 => [(6,2)]
  | 46 => [(8,4)]
  | 47 => [(6,4)]
  | 48 => [(1,2)]
  | 49 => [(7,4)]
  | 50 => [(8,5)]
  | 51 => [(1,0)]
  | 52 => [(7,1)]
  | 53 => [(7,5)]
  | 54 => [(0,3)]
  | 55 => [(8,1)]
  | 56 => [(7,2),(8,2)]
  | 57 => [(4,0),(8,0)]
  | 58 => [(7,3)]
  | 59 => [(4,2)]
  | _ => [(5,3)]
def root6Node49Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,1)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(3,3),(7,3)]
  | 12 => some [(5,2)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(2,3)]
  | 18 => some [(0,1)]
  | 19 => some [(6,2)]
  | 20 => some [(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(4,5)]
  | 27 => some [(1,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2)]
  | 36 => some [(4,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(5,1)]
  | 44 => some [(0,1)]
  | 45 => some [(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(6,4)]
  | 48 => some [(1,2)]
  | 49 => some [(7,4)]
  | 50 => some [(8,5)]
  | 51 => some [(1,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(8,1)]
  | 56 => some [(7,2),(8,2)]
  | 57 => some [(4,0),(8,0)]
  | 58 => some [(7,3)]
  | 59 => some [(4,2)]
  | _ => some [(5,3)]
theorem root6Node49Domains2_fast_eq : root6Node49Domains2 = expandDomains root6Node49Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node49Domains2 v = expandDomains root6Node49Domains2Fast v from by decide) v
theorem root6Node49Step2Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root6Node49Domains1 root6Node49Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node49Domains1 root6Node49Domains2
    root6Node49Domains1Fast root6Node49Domains2Fast
    root6Node49Domains1_fast_eq root6Node49Domains2_fast_eq (by decide)
theorem root6Node49Step2_checked :
    checkReplacement table39 root6Node49Domains1 root6Node49Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node49Step2Chunk0_0_checked, root6Node49Step2Chunk0_1_checked, root6Node49Step2Chunk0_2_checked, root6Node49Step2Chunk0_3_checked, root6Node49Step2Chunk0_4_checked, root6Node49Step2Chunk0_5_checked, root6Node49Step2Chunk1_0_checked, root6Node49Step2Chunk1_1_checked, root6Node49Step2Chunk1_2_checked, root6Node49Step2Chunk1_3_checked, root6Node49Step2Chunk1_4_checked, root6Node49Step2Chunk1_5_checked, root6Node49Step2Chunk2_0_checked, root6Node49Step2Chunk2_1_checked, root6Node49Step2Chunk2_2_checked, root6Node49Step2Chunk2_3_checked, root6Node49Step2Chunk2_4_checked, root6Node49Step2Chunk2_5_checked, root6Node49Step2Chunk3_0_checked, root6Node49Step2Chunk3_1_checked, root6Node49Step2Chunk3_2_checked, root6Node49Step2Chunk3_3_checked, root6Node49Step2Chunk3_4_checked, root6Node49Step2Chunk3_5_checked, root6Node49Step2Chunk4_0_checked, root6Node49Step2Chunk4_1_checked, root6Node49Step2Chunk4_2_checked, root6Node49Step2Chunk4_3_checked, root6Node49Step2Chunk4_4_checked, root6Node49Step2Chunk4_5_checked, root6Node49Step2Chunk5_0_checked, root6Node49Step2Chunk5_1_checked, root6Node49Step2Chunk5_2_checked, root6Node49Step2Chunk5_3_checked, root6Node49Step2Chunk5_4_checked, root6Node49Step2Chunk5_5_checked, root6Node49Step2Chunk6_0_checked, root6Node49Step2Chunk6_1_checked, root6Node49Step2Chunk6_2_checked, root6Node49Step2Chunk6_3_checked, root6Node49Step2Chunk6_4_checked, root6Node49Step2Chunk6_5_checked, root6Node49Step2Chunk7_0_checked, root6Node49Step2Chunk7_1_checked, root6Node49Step2Chunk7_2_checked, root6Node49Step2Chunk7_3_checked, root6Node49Step2Chunk7_4_checked, root6Node49Step2Chunk7_5_checked, root6Node49Step2Chunk8_0_checked, root6Node49Step2Chunk8_1_checked, root6Node49Step2Chunk8_2_checked, root6Node49Step2Chunk8_3_checked, root6Node49Step2Chunk8_4_checked, root6Node49Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
