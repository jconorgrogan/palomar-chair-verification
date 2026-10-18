module

public import SpectreFinite.RadiusFourRoot8Part1
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable10
public import SpectreFinite.RadiusFourTable23
public import SpectreFinite.RadiusFourTable27
public import SpectreFinite.RadiusFourTable35
public import SpectreFinite.RadiusFourTable39

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node2Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(5,1),(8,1)]
  | 3 => [(0,1),(6,5)]
  | 4 => [(0,4),(6,2)]
  | 5 => [(4,5),(8,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0),(7,0)]
  | 10 => [(4,3),(7,1)]
  | 11 => [(0,0),(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(4,0),(7,4)]
  | 17 => [(1,3),(6,3),(7,3)]
  | 18 => [(0,2),(1,5)]
  | 19 => [(1,1),(6,1)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1),(5,1),(8,1)]
  | 24 => [(0,1),(0,2),(6,5)]
  | 25 => [(0,4),(1,1),(6,2)]
  | 26 => [(0,5),(1,2),(3,2)]
  | 27 => [(2,0),(4,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3),(8,3)]
  | 32 => [(5,2),(5,5)]
  | 33 => [(1,0),(3,0),(5,0),(7,0)]
  | 34 => [(2,1),(2,3),(2,5),(4,5)]
  | 35 => [(3,1),(5,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(1,4),(6,4)]
  | 40 => [(0,5),(1,2)]
  | 41 => [(4,4),(8,4)]
  | 42 => [(0,0),(6,4)]
  | 43 => [(4,5),(8,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(0,3),(6,0)]
  | 48 => [(7,1),(8,1)]
  | 49 => [(1,5),(7,5)]
  | 50 => [(7,2),(8,2)]
  | 51 => [(4,0),(8,0)]
  | 52 => [(7,3)]
  | 53 => [(4,2),(8,2)]
  | 54 => [(5,0),(5,3),(8,0)]
  | 55 => [(4,5),(7,3),(8,5)]
  | 56 => [(5,1),(5,4),(8,1)]
  | 57 => [(0,1),(6,4)]
  | 58 => [(1,2),(6,2)]
  | 59 => [(7,4),(8,4)]
  | _ => [(0,0),(6,3),(6,4)]
def root8Node2Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1),(8,1)]
  | 3 => some [(0,1),(6,5)]
  | 4 => some [(0,4),(6,2)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0),(7,0)]
  | 10 => some [(4,3),(7,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0),(7,4)]
  | 17 => some [(1,3),(6,3),(7,3)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1),(5,1),(8,1)]
  | 24 => some [(0,1),(0,2),(6,5)]
  | 25 => some [(0,4),(1,1),(6,2)]
  | 26 => some [(0,5),(1,2),(3,2)]
  | 27 => some [(2,0),(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5)]
  | 33 => some [(1,0),(3,0),(5,0),(7,0)]
  | 34 => some [(2,1),(2,3),(2,5),(4,5)]
  | 35 => some [(3,1),(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,5),(1,2)]
  | 41 => some [(4,4),(8,4)]
  | 42 => some [(0,0),(6,4)]
  | 43 => some [(4,5),(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3),(6,0)]
  | 48 => some [(7,1),(8,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2),(8,2)]
  | 54 => some [(5,0),(5,3),(8,0)]
  | 55 => some [(4,5),(7,3),(8,5)]
  | 56 => some [(5,1),(5,4),(8,1)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(7,4),(8,4)]
  | _ => some [(0,0),(6,3),(6,4)]
theorem root8Node2Domains3_fast_eq : root8Node2Domains3 = expandDomains root8Node2Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node2Domains3 v = expandDomains root8Node2Domains3Fast v from by decide) v
theorem root8Node2Step3Chunk0_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_0⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk0_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_1⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk0_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_2⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk0_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_3⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk0_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_4⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk0_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_5⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk1_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_0⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk1_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_1⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk1_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_2⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk1_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_3⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk1_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_4⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk1_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_5⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk2_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_0⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk2_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_1⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk2_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_2⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk2_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_3⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk2_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_4⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk2_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_5⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk3_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_0⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk3_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_1⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk3_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_2⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk3_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_3⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk3_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_4⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk3_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_5⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk4_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_0⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk4_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_1⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk4_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_2⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk4_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_3⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk4_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_4⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk4_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_5⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk5_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_0⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk5_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_1⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk5_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_2⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk5_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_3⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk5_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_4⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk5_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_5⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk6_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_0⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk6_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_1⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk6_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_2⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk6_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_3⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk6_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_4⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk6_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_5⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk7_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_0⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk7_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_1⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk7_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_2⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk7_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_3⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk7_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_4⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk7_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_5⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk8_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_0⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk8_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_1⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk8_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_2⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk8_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_3⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk8_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_4⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3Chunk8_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_5⟩
      root8Node2Domains2 root8Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains2 root8Node2Domains3
    root8Node2Domains2Fast root8Node2Domains3Fast
    root8Node2Domains2_fast_eq root8Node2Domains3_fast_eq (by decide)
theorem root8Node2Step3_checked :
    checkReplacement table10 root8Node2Domains2 root8Node2Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node2Step3Chunk0_0_checked, root8Node2Step3Chunk0_1_checked, root8Node2Step3Chunk0_2_checked, root8Node2Step3Chunk0_3_checked, root8Node2Step3Chunk0_4_checked, root8Node2Step3Chunk0_5_checked, root8Node2Step3Chunk1_0_checked, root8Node2Step3Chunk1_1_checked, root8Node2Step3Chunk1_2_checked, root8Node2Step3Chunk1_3_checked, root8Node2Step3Chunk1_4_checked, root8Node2Step3Chunk1_5_checked, root8Node2Step3Chunk2_0_checked, root8Node2Step3Chunk2_1_checked, root8Node2Step3Chunk2_2_checked, root8Node2Step3Chunk2_3_checked, root8Node2Step3Chunk2_4_checked, root8Node2Step3Chunk2_5_checked, root8Node2Step3Chunk3_0_checked, root8Node2Step3Chunk3_1_checked, root8Node2Step3Chunk3_2_checked, root8Node2Step3Chunk3_3_checked, root8Node2Step3Chunk3_4_checked, root8Node2Step3Chunk3_5_checked, root8Node2Step3Chunk4_0_checked, root8Node2Step3Chunk4_1_checked, root8Node2Step3Chunk4_2_checked, root8Node2Step3Chunk4_3_checked, root8Node2Step3Chunk4_4_checked, root8Node2Step3Chunk4_5_checked, root8Node2Step3Chunk5_0_checked, root8Node2Step3Chunk5_1_checked, root8Node2Step3Chunk5_2_checked, root8Node2Step3Chunk5_3_checked, root8Node2Step3Chunk5_4_checked, root8Node2Step3Chunk5_5_checked, root8Node2Step3Chunk6_0_checked, root8Node2Step3Chunk6_1_checked, root8Node2Step3Chunk6_2_checked, root8Node2Step3Chunk6_3_checked, root8Node2Step3Chunk6_4_checked, root8Node2Step3Chunk6_5_checked, root8Node2Step3Chunk7_0_checked, root8Node2Step3Chunk7_1_checked, root8Node2Step3Chunk7_2_checked, root8Node2Step3Chunk7_3_checked, root8Node2Step3Chunk7_4_checked, root8Node2Step3Chunk7_5_checked, root8Node2Step3Chunk8_0_checked, root8Node2Step3Chunk8_1_checked, root8Node2Step3Chunk8_2_checked, root8Node2Step3Chunk8_3_checked, root8Node2Step3Chunk8_4_checked, root8Node2Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node2Domains4 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(5,1),(8,1)]
  | 3 => [(0,1),(6,5)]
  | 4 => [(0,4),(6,2)]
  | 5 => [(4,5),(8,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0),(7,0)]
  | 10 => [(4,3),(7,1)]
  | 11 => [(0,0),(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(4,0),(7,4)]
  | 17 => [(1,3),(6,3),(7,3)]
  | 18 => [(0,2),(1,5)]
  | 19 => [(1,1),(6,1)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1),(5,1),(8,1)]
  | 24 => [(0,1),(0,2),(6,5)]
  | 25 => [(0,4),(1,1),(6,2)]
  | 26 => [(0,5),(1,2),(3,2)]
  | 27 => [(2,0),(4,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3),(8,3)]
  | 32 => [(5,2),(5,5)]
  | 33 => [(1,0),(3,0),(5,0),(7,0)]
  | 34 => [(2,1),(2,3),(2,5),(4,5)]
  | 35 => [(3,1),(5,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(1,4),(6,4)]
  | 40 => [(0,5),(1,2)]
  | 41 => [(4,4),(8,4)]
  | 42 => [(0,0),(6,4)]
  | 43 => [(4,5),(8,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(0,3),(6,0)]
  | 48 => [(7,1),(8,1)]
  | 49 => [(1,5),(7,5)]
  | 50 => [(7,2),(8,2)]
  | 51 => [(4,0),(8,0)]
  | 52 => [(7,3)]
  | 53 => [(4,2),(8,2)]
  | 54 => [(5,0),(5,3),(8,0)]
  | 55 => [(4,5),(7,3),(8,5)]
  | 56 => [(5,1),(5,4)]
  | 57 => [(0,1),(6,4)]
  | 58 => [(1,2),(6,2)]
  | 59 => [(7,4),(8,4)]
  | _ => [(0,0),(6,3),(6,4)]
def root8Node2Domains4Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1),(8,1)]
  | 3 => some [(0,1),(6,5)]
  | 4 => some [(0,4),(6,2)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0),(7,0)]
  | 10 => some [(4,3),(7,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0),(7,4)]
  | 17 => some [(1,3),(6,3),(7,3)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1),(5,1),(8,1)]
  | 24 => some [(0,1),(0,2),(6,5)]
  | 25 => some [(0,4),(1,1),(6,2)]
  | 26 => some [(0,5),(1,2),(3,2)]
  | 27 => some [(2,0),(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5)]
  | 33 => some [(1,0),(3,0),(5,0),(7,0)]
  | 34 => some [(2,1),(2,3),(2,5),(4,5)]
  | 35 => some [(3,1),(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,5),(1,2)]
  | 41 => some [(4,4),(8,4)]
  | 42 => some [(0,0),(6,4)]
  | 43 => some [(4,5),(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3),(6,0)]
  | 48 => some [(7,1),(8,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2),(8,2)]
  | 54 => some [(5,0),(5,3),(8,0)]
  | 55 => some [(4,5),(7,3),(8,5)]
  | 56 => some [(5,1),(5,4)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(7,4),(8,4)]
  | _ => some [(0,0),(6,3),(6,4)]
theorem root8Node2Domains4_fast_eq : root8Node2Domains4 = expandDomains root8Node2Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node2Domains4 v = expandDomains root8Node2Domains4Fast v from by decide) v
theorem root8Node2Step4Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root8Node2Domains3 root8Node2Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains3 root8Node2Domains4
    root8Node2Domains3Fast root8Node2Domains4Fast
    root8Node2Domains3_fast_eq root8Node2Domains4_fast_eq (by decide)
theorem root8Node2Step4_checked :
    checkReplacement table35 root8Node2Domains3 root8Node2Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node2Step4Chunk0_0_checked, root8Node2Step4Chunk0_1_checked, root8Node2Step4Chunk0_2_checked, root8Node2Step4Chunk0_3_checked, root8Node2Step4Chunk0_4_checked, root8Node2Step4Chunk0_5_checked, root8Node2Step4Chunk1_0_checked, root8Node2Step4Chunk1_1_checked, root8Node2Step4Chunk1_2_checked, root8Node2Step4Chunk1_3_checked, root8Node2Step4Chunk1_4_checked, root8Node2Step4Chunk1_5_checked, root8Node2Step4Chunk2_0_checked, root8Node2Step4Chunk2_1_checked, root8Node2Step4Chunk2_2_checked, root8Node2Step4Chunk2_3_checked, root8Node2Step4Chunk2_4_checked, root8Node2Step4Chunk2_5_checked, root8Node2Step4Chunk3_0_checked, root8Node2Step4Chunk3_1_checked, root8Node2Step4Chunk3_2_checked, root8Node2Step4Chunk3_3_checked, root8Node2Step4Chunk3_4_checked, root8Node2Step4Chunk3_5_checked, root8Node2Step4Chunk4_0_checked, root8Node2Step4Chunk4_1_checked, root8Node2Step4Chunk4_2_checked, root8Node2Step4Chunk4_3_checked, root8Node2Step4Chunk4_4_checked, root8Node2Step4Chunk4_5_checked, root8Node2Step4Chunk5_0_checked, root8Node2Step4Chunk5_1_checked, root8Node2Step4Chunk5_2_checked, root8Node2Step4Chunk5_3_checked, root8Node2Step4Chunk5_4_checked, root8Node2Step4Chunk5_5_checked, root8Node2Step4Chunk6_0_checked, root8Node2Step4Chunk6_1_checked, root8Node2Step4Chunk6_2_checked, root8Node2Step4Chunk6_3_checked, root8Node2Step4Chunk6_4_checked, root8Node2Step4Chunk6_5_checked, root8Node2Step4Chunk7_0_checked, root8Node2Step4Chunk7_1_checked, root8Node2Step4Chunk7_2_checked, root8Node2Step4Chunk7_3_checked, root8Node2Step4Chunk7_4_checked, root8Node2Step4Chunk7_5_checked, root8Node2Step4Chunk8_0_checked, root8Node2Step4Chunk8_1_checked, root8Node2Step4Chunk8_2_checked, root8Node2Step4Chunk8_3_checked, root8Node2Step4Chunk8_4_checked, root8Node2Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node3Domains0 : Domains 61 State := restrict root8Node2Domains4 2 (5,1)
def root8Node3Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1),(6,5)]
  | 4 => some [(0,4),(6,2)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0),(7,0)]
  | 10 => some [(4,3),(7,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0),(7,4)]
  | 17 => some [(1,3),(6,3),(7,3)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1),(5,1),(8,1)]
  | 24 => some [(0,1),(0,2),(6,5)]
  | 25 => some [(0,4),(1,1),(6,2)]
  | 26 => some [(0,5),(1,2),(3,2)]
  | 27 => some [(2,0),(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5)]
  | 33 => some [(1,0),(3,0),(5,0),(7,0)]
  | 34 => some [(2,1),(2,3),(2,5),(4,5)]
  | 35 => some [(3,1),(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,5),(1,2)]
  | 41 => some [(4,4),(8,4)]
  | 42 => some [(0,0),(6,4)]
  | 43 => some [(4,5),(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3),(6,0)]
  | 48 => some [(7,1),(8,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2),(8,2)]
  | 54 => some [(5,0),(5,3),(8,0)]
  | 55 => some [(4,5),(7,3),(8,5)]
  | 56 => some [(5,1),(5,4)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(7,4),(8,4)]
  | _ => some [(0,0),(6,3),(6,4)]
theorem root8Node3Domains0_fast_eq : root8Node3Domains0 = expandDomains root8Node3Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node3Domains0 v = expandDomains root8Node3Domains0Fast v from by decide) v
def root8Node3Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(4,5),(8,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(0,0),(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(4,0)]
  | 17 => [(7,3)]
  | 18 => [(0,2),(1,5)]
  | 19 => [(1,1),(6,1)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(0,5),(1,2),(3,2)]
  | 27 => [(2,0),(4,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(8,3)]
  | 32 => [(5,5)]
  | 33 => [(1,0)]
  | 34 => [(2,1)]
  | 35 => [(3,1),(5,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(1,4)]
  | 40 => [(0,5)]
  | 41 => [(4,4)]
  | 42 => [(0,0)]
  | 43 => [(4,5),(8,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(6,0)]
  | 48 => [(7,1)]
  | 49 => [(1,5)]
  | 50 => [(7,2),(8,2)]
  | 51 => [(4,0),(8,0)]
  | 52 => [(7,3)]
  | 53 => [(4,2),(8,2)]
  | 54 => [(5,0),(5,3),(8,0)]
  | 55 => [(4,5),(7,3),(8,5)]
  | 56 => [(5,1),(5,4)]
  | 57 => [(0,1),(6,4)]
  | 58 => [(1,2),(6,2)]
  | 59 => [(7,4),(8,4)]
  | _ => [(0,0),(6,3),(6,4)]
def root8Node3Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(0,5),(1,2),(3,2)]
  | 27 => some [(2,0),(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5)]
  | 33 => some [(1,0)]
  | 34 => some [(2,1)]
  | 35 => some [(3,1),(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(4,4)]
  | 42 => some [(0,0)]
  | 43 => some [(4,5),(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(1,5)]
  | 50 => some [(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2),(8,2)]
  | 54 => some [(5,0),(5,3),(8,0)]
  | 55 => some [(4,5),(7,3),(8,5)]
  | 56 => some [(5,1),(5,4)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(7,4),(8,4)]
  | _ => some [(0,0),(6,3),(6,4)]
theorem root8Node3Domains1_fast_eq : root8Node3Domains1 = expandDomains root8Node3Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node3Domains1 v = expandDomains root8Node3Domains1Fast v from by decide) v
theorem root8Node3Step1Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root8Node3Domains0 root8Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains0 root8Node3Domains1
    root8Node3Domains0Fast root8Node3Domains1Fast
    root8Node3Domains0_fast_eq root8Node3Domains1_fast_eq (by decide)
theorem root8Node3Step1_checked :
    checkReplacement table23 root8Node3Domains0 root8Node3Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node3Step1Chunk0_0_checked, root8Node3Step1Chunk0_1_checked, root8Node3Step1Chunk0_2_checked, root8Node3Step1Chunk0_3_checked, root8Node3Step1Chunk0_4_checked, root8Node3Step1Chunk0_5_checked, root8Node3Step1Chunk1_0_checked, root8Node3Step1Chunk1_1_checked, root8Node3Step1Chunk1_2_checked, root8Node3Step1Chunk1_3_checked, root8Node3Step1Chunk1_4_checked, root8Node3Step1Chunk1_5_checked, root8Node3Step1Chunk2_0_checked, root8Node3Step1Chunk2_1_checked, root8Node3Step1Chunk2_2_checked, root8Node3Step1Chunk2_3_checked, root8Node3Step1Chunk2_4_checked, root8Node3Step1Chunk2_5_checked, root8Node3Step1Chunk3_0_checked, root8Node3Step1Chunk3_1_checked, root8Node3Step1Chunk3_2_checked, root8Node3Step1Chunk3_3_checked, root8Node3Step1Chunk3_4_checked, root8Node3Step1Chunk3_5_checked, root8Node3Step1Chunk4_0_checked, root8Node3Step1Chunk4_1_checked, root8Node3Step1Chunk4_2_checked, root8Node3Step1Chunk4_3_checked, root8Node3Step1Chunk4_4_checked, root8Node3Step1Chunk4_5_checked, root8Node3Step1Chunk5_0_checked, root8Node3Step1Chunk5_1_checked, root8Node3Step1Chunk5_2_checked, root8Node3Step1Chunk5_3_checked, root8Node3Step1Chunk5_4_checked, root8Node3Step1Chunk5_5_checked, root8Node3Step1Chunk6_0_checked, root8Node3Step1Chunk6_1_checked, root8Node3Step1Chunk6_2_checked, root8Node3Step1Chunk6_3_checked, root8Node3Step1Chunk6_4_checked, root8Node3Step1Chunk6_5_checked, root8Node3Step1Chunk7_0_checked, root8Node3Step1Chunk7_1_checked, root8Node3Step1Chunk7_2_checked, root8Node3Step1Chunk7_3_checked, root8Node3Step1Chunk7_4_checked, root8Node3Step1Chunk7_5_checked, root8Node3Step1Chunk8_0_checked, root8Node3Step1Chunk8_1_checked, root8Node3Step1Chunk8_2_checked, root8Node3Step1Chunk8_3_checked, root8Node3Step1Chunk8_4_checked, root8Node3Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node3Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(4,5),(8,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(0,0),(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(4,0)]
  | 17 => [(7,3)]
  | 18 => [(0,2),(1,5)]
  | 19 => [(1,1),(6,1)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(0,5),(1,2),(3,2)]
  | 27 => [(2,0),(4,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(8,3)]
  | 32 => [(5,5)]
  | 33 => [(1,0)]
  | 34 => [(2,1)]
  | 35 => [(3,1),(5,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(1,4)]
  | 40 => [(0,5)]
  | 41 => [(4,4)]
  | 42 => [(0,0)]
  | 43 => [(4,5),(8,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(6,0)]
  | 48 => [(7,1)]
  | 49 => [(1,5)]
  | 50 => [(7,2),(8,2)]
  | 51 => [(4,0),(8,0)]
  | 52 => [(7,3)]
  | 53 => [(8,2)]
  | 54 => [(5,0)]
  | 55 => [(4,5)]
  | 56 => [(5,1),(5,4)]
  | 57 => [(0,1),(6,4)]
  | 58 => [(1,2),(6,2)]
  | 59 => [(8,4)]
  | _ => [(0,0)]
def root8Node3Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(0,5),(1,2),(3,2)]
  | 27 => some [(2,0),(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5)]
  | 33 => some [(1,0)]
  | 34 => some [(2,1)]
  | 35 => some [(3,1),(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(4,4)]
  | 42 => some [(0,0)]
  | 43 => some [(4,5),(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(1,5)]
  | 50 => some [(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(8,2)]
  | 54 => some [(5,0)]
  | 55 => some [(4,5)]
  | 56 => some [(5,1),(5,4)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(0,0)]
theorem root8Node3Domains2_fast_eq : root8Node3Domains2 = expandDomains root8Node3Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node3Domains2 v = expandDomains root8Node3Domains2Fast v from by decide) v
theorem root8Node3Step2Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root8Node3Domains1 root8Node3Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node3Domains1 root8Node3Domains2
    root8Node3Domains1Fast root8Node3Domains2Fast
    root8Node3Domains1_fast_eq root8Node3Domains2_fast_eq (by decide)
theorem root8Node3Step2_checked :
    checkReplacement table39 root8Node3Domains1 root8Node3Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node3Step2Chunk0_0_checked, root8Node3Step2Chunk0_1_checked, root8Node3Step2Chunk0_2_checked, root8Node3Step2Chunk0_3_checked, root8Node3Step2Chunk0_4_checked, root8Node3Step2Chunk0_5_checked, root8Node3Step2Chunk1_0_checked, root8Node3Step2Chunk1_1_checked, root8Node3Step2Chunk1_2_checked, root8Node3Step2Chunk1_3_checked, root8Node3Step2Chunk1_4_checked, root8Node3Step2Chunk1_5_checked, root8Node3Step2Chunk2_0_checked, root8Node3Step2Chunk2_1_checked, root8Node3Step2Chunk2_2_checked, root8Node3Step2Chunk2_3_checked, root8Node3Step2Chunk2_4_checked, root8Node3Step2Chunk2_5_checked, root8Node3Step2Chunk3_0_checked, root8Node3Step2Chunk3_1_checked, root8Node3Step2Chunk3_2_checked, root8Node3Step2Chunk3_3_checked, root8Node3Step2Chunk3_4_checked, root8Node3Step2Chunk3_5_checked, root8Node3Step2Chunk4_0_checked, root8Node3Step2Chunk4_1_checked, root8Node3Step2Chunk4_2_checked, root8Node3Step2Chunk4_3_checked, root8Node3Step2Chunk4_4_checked, root8Node3Step2Chunk4_5_checked, root8Node3Step2Chunk5_0_checked, root8Node3Step2Chunk5_1_checked, root8Node3Step2Chunk5_2_checked, root8Node3Step2Chunk5_3_checked, root8Node3Step2Chunk5_4_checked, root8Node3Step2Chunk5_5_checked, root8Node3Step2Chunk6_0_checked, root8Node3Step2Chunk6_1_checked, root8Node3Step2Chunk6_2_checked, root8Node3Step2Chunk6_3_checked, root8Node3Step2Chunk6_4_checked, root8Node3Step2Chunk6_5_checked, root8Node3Step2Chunk7_0_checked, root8Node3Step2Chunk7_1_checked, root8Node3Step2Chunk7_2_checked, root8Node3Step2Chunk7_3_checked, root8Node3Step2Chunk7_4_checked, root8Node3Step2Chunk7_5_checked, root8Node3Step2Chunk8_0_checked, root8Node3Step2Chunk8_1_checked, root8Node3Step2Chunk8_2_checked, root8Node3Step2Chunk8_3_checked, root8Node3Step2Chunk8_4_checked, root8Node3Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node4Domains0 : Domains 61 State := restrict root8Node3Domains2 5 (4,5)
def root8Node4Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(4,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(0,5),(1,2),(3,2)]
  | 27 => some [(2,0),(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5)]
  | 33 => some [(1,0)]
  | 34 => some [(2,1)]
  | 35 => some [(3,1),(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(4,4)]
  | 42 => some [(0,0)]
  | 43 => some [(4,5),(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(1,5)]
  | 50 => some [(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(8,2)]
  | 54 => some [(5,0)]
  | 55 => some [(4,5)]
  | 56 => some [(5,1),(5,4)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(0,0)]
theorem root8Node4Domains0_fast_eq : root8Node4Domains0 = expandDomains root8Node4Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node4Domains0 v = expandDomains root8Node4Domains0Fast v from by decide) v
def root8Node4Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(4,0)]
  | 17 => [(7,3)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(0,5)]
  | 27 => [(2,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(8,3)]
  | 32 => [(5,5)]
  | 33 => [(1,0)]
  | 34 => [(2,1)]
  | 35 => [(3,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(1,4)]
  | 40 => [(0,5)]
  | 41 => [(4,4)]
  | 42 => [(0,0)]
  | 43 => [(4,5)]
  | 44 => [(1,0)]
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
  | 56 => [(5,1),(5,4)]
  | 57 => [(0,1),(6,4)]
  | 58 => [(1,2),(6,2)]
  | 59 => [(8,4)]
  | _ => [(0,0)]
def root8Node4Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(4,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(0,5)]
  | 27 => some [(2,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5)]
  | 33 => some [(1,0)]
  | 34 => some [(2,1)]
  | 35 => some [(3,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(4,4)]
  | 42 => some [(0,0)]
  | 43 => some [(4,5)]
  | 44 => some [(1,0)]
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
  | 56 => some [(5,1),(5,4)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(0,0)]
theorem root8Node4Domains1_fast_eq : root8Node4Domains1 = expandDomains root8Node4Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node4Domains1 v = expandDomains root8Node4Domains1Fast v from by decide) v
theorem root8Node4Step1Chunk0_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_0⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk0_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_1⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk0_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_2⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk0_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_3⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk0_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_4⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk0_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_5⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk1_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_0⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk1_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_1⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk1_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_2⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk1_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_3⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk1_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_4⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk1_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_5⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk2_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_0⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk2_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_1⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk2_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_2⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk2_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_3⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk2_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_4⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk2_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_5⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk3_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_0⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk3_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_1⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk3_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_2⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk3_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_3⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk3_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_4⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk3_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_5⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk4_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_0⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk4_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_1⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk4_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_2⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk4_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_3⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk4_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_4⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk4_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_5⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk5_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_0⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk5_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_1⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk5_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_2⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk5_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_3⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk5_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_4⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk5_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_5⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk6_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_0⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk6_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_1⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk6_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_2⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk6_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_3⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk6_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_4⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk6_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_5⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk7_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_0⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk7_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_1⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk7_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_2⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk7_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_3⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk7_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_4⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk7_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_5⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk8_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_0⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk8_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_1⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk8_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_2⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk8_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_3⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk8_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_4⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1Chunk8_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_5⟩
      root8Node4Domains0 root8Node4Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node4Domains0 root8Node4Domains1
    root8Node4Domains0Fast root8Node4Domains1Fast
    root8Node4Domains0_fast_eq root8Node4Domains1_fast_eq (by decide)
theorem root8Node4Step1_checked :
    checkReplacement table27 root8Node4Domains0 root8Node4Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node4Step1Chunk0_0_checked, root8Node4Step1Chunk0_1_checked, root8Node4Step1Chunk0_2_checked, root8Node4Step1Chunk0_3_checked, root8Node4Step1Chunk0_4_checked, root8Node4Step1Chunk0_5_checked, root8Node4Step1Chunk1_0_checked, root8Node4Step1Chunk1_1_checked, root8Node4Step1Chunk1_2_checked, root8Node4Step1Chunk1_3_checked, root8Node4Step1Chunk1_4_checked, root8Node4Step1Chunk1_5_checked, root8Node4Step1Chunk2_0_checked, root8Node4Step1Chunk2_1_checked, root8Node4Step1Chunk2_2_checked, root8Node4Step1Chunk2_3_checked, root8Node4Step1Chunk2_4_checked, root8Node4Step1Chunk2_5_checked, root8Node4Step1Chunk3_0_checked, root8Node4Step1Chunk3_1_checked, root8Node4Step1Chunk3_2_checked, root8Node4Step1Chunk3_3_checked, root8Node4Step1Chunk3_4_checked, root8Node4Step1Chunk3_5_checked, root8Node4Step1Chunk4_0_checked, root8Node4Step1Chunk4_1_checked, root8Node4Step1Chunk4_2_checked, root8Node4Step1Chunk4_3_checked, root8Node4Step1Chunk4_4_checked, root8Node4Step1Chunk4_5_checked, root8Node4Step1Chunk5_0_checked, root8Node4Step1Chunk5_1_checked, root8Node4Step1Chunk5_2_checked, root8Node4Step1Chunk5_3_checked, root8Node4Step1Chunk5_4_checked, root8Node4Step1Chunk5_5_checked, root8Node4Step1Chunk6_0_checked, root8Node4Step1Chunk6_1_checked, root8Node4Step1Chunk6_2_checked, root8Node4Step1Chunk6_3_checked, root8Node4Step1Chunk6_4_checked, root8Node4Step1Chunk6_5_checked, root8Node4Step1Chunk7_0_checked, root8Node4Step1Chunk7_1_checked, root8Node4Step1Chunk7_2_checked, root8Node4Step1Chunk7_3_checked, root8Node4Step1Chunk7_4_checked, root8Node4Step1Chunk7_5_checked, root8Node4Step1Chunk8_0_checked, root8Node4Step1Chunk8_1_checked, root8Node4Step1Chunk8_2_checked, root8Node4Step1Chunk8_3_checked, root8Node4Step1Chunk8_4_checked, root8Node4Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
