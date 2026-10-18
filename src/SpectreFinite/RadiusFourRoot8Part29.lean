module

public import SpectreFinite.RadiusFourRoot8Part28
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable23
public import SpectreFinite.RadiusFourTable37

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node94Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(5,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(2,3),(4,3)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(1,4),(6,4)]
  | 17 => [(0,5),(1,2)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3),(6,0)]
  | 25 => [(3,1),(5,1),(7,1)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2),(8,2)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5),(8,5)]
  | 35 => [(5,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(7,4),(8,4)]
  | 42 => [(0,0),(1,3)]
  | 43 => [(8,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(0,3)]
  | 48 => [(8,1)]
  | 49 => [(1,5),(6,5)]
  | 50 => [(7,2),(8,2)]
  | 51 => [(4,0),(8,0)]
  | 52 => [(7,3)]
  | 53 => [(4,2)]
  | 54 => [(5,3)]
  | 55 => [(8,5)]
  | 56 => [(5,1),(5,4)]
  | 57 => [(0,1),(6,4)]
  | 58 => [(1,2),(6,2)]
  | 59 => [(7,4)]
  | _ => [(6,3)]
def root8Node94Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(2,3),(4,3)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(3,1),(5,1),(7,1)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(8,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(1,3)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(1,5),(6,5)]
  | 50 => some [(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,1),(5,4)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root8Node94Domains3_fast_eq : root8Node94Domains3 = expandDomains root8Node94Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node94Domains3 v = expandDomains root8Node94Domains3Fast v from by decide) v
theorem root8Node94Step3Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root8Node94Domains2 root8Node94Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node94Domains2 root8Node94Domains3
    root8Node94Domains2Fast root8Node94Domains3Fast
    root8Node94Domains2_fast_eq root8Node94Domains3_fast_eq (by decide)
theorem root8Node94Step3_checked :
    checkReplacement table23 root8Node94Domains2 root8Node94Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node94Step3Chunk0_0_checked, root8Node94Step3Chunk0_1_checked, root8Node94Step3Chunk0_2_checked, root8Node94Step3Chunk0_3_checked, root8Node94Step3Chunk0_4_checked, root8Node94Step3Chunk0_5_checked, root8Node94Step3Chunk1_0_checked, root8Node94Step3Chunk1_1_checked, root8Node94Step3Chunk1_2_checked, root8Node94Step3Chunk1_3_checked, root8Node94Step3Chunk1_4_checked, root8Node94Step3Chunk1_5_checked, root8Node94Step3Chunk2_0_checked, root8Node94Step3Chunk2_1_checked, root8Node94Step3Chunk2_2_checked, root8Node94Step3Chunk2_3_checked, root8Node94Step3Chunk2_4_checked, root8Node94Step3Chunk2_5_checked, root8Node94Step3Chunk3_0_checked, root8Node94Step3Chunk3_1_checked, root8Node94Step3Chunk3_2_checked, root8Node94Step3Chunk3_3_checked, root8Node94Step3Chunk3_4_checked, root8Node94Step3Chunk3_5_checked, root8Node94Step3Chunk4_0_checked, root8Node94Step3Chunk4_1_checked, root8Node94Step3Chunk4_2_checked, root8Node94Step3Chunk4_3_checked, root8Node94Step3Chunk4_4_checked, root8Node94Step3Chunk4_5_checked, root8Node94Step3Chunk5_0_checked, root8Node94Step3Chunk5_1_checked, root8Node94Step3Chunk5_2_checked, root8Node94Step3Chunk5_3_checked, root8Node94Step3Chunk5_4_checked, root8Node94Step3Chunk5_5_checked, root8Node94Step3Chunk6_0_checked, root8Node94Step3Chunk6_1_checked, root8Node94Step3Chunk6_2_checked, root8Node94Step3Chunk6_3_checked, root8Node94Step3Chunk6_4_checked, root8Node94Step3Chunk6_5_checked, root8Node94Step3Chunk7_0_checked, root8Node94Step3Chunk7_1_checked, root8Node94Step3Chunk7_2_checked, root8Node94Step3Chunk7_3_checked, root8Node94Step3Chunk7_4_checked, root8Node94Step3Chunk7_5_checked, root8Node94Step3Chunk8_0_checked, root8Node94Step3Chunk8_1_checked, root8Node94Step3Chunk8_2_checked, root8Node94Step3Chunk8_3_checked, root8Node94Step3Chunk8_4_checked, root8Node94Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node95Domains0 : Domains 61 State := restrict root8Node94Domains3 10 (2,3)
def root8Node95Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(2,3)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(3,1),(5,1),(7,1)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(8,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(1,3)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(1,5),(6,5)]
  | 50 => some [(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,1),(5,4)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root8Node95Domains0_fast_eq : root8Node95Domains0 = expandDomains root8Node95Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node95Domains0 v = expandDomains root8Node95Domains0Fast v from by decide) v
def root8Node95Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(5,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(2,3)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(6,4)]
  | 17 => [(1,2)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3)]
  | 25 => [(5,1)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2)]
  | 33 => [(5,3)]
  | 34 => [(8,5)]
  | 35 => [(5,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(7,4)]
  | 42 => [(1,3)]
  | 43 => [(8,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(0,3)]
  | 48 => [(8,1)]
  | 49 => [(6,5)]
  | 50 => [(7,2),(8,2)]
  | 51 => [(4,0),(8,0)]
  | 52 => [(7,3)]
  | 53 => [(4,2)]
  | 54 => [(5,3)]
  | 55 => [(8,5)]
  | 56 => [(5,1),(5,4)]
  | 57 => [(0,1),(6,4)]
  | 58 => [(1,2),(6,2)]
  | 59 => [(7,4)]
  | _ => [(6,3)]
def root8Node95Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(2,3)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3)]
  | 25 => some [(5,1)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,1),(5,4)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root8Node95Domains1_fast_eq : root8Node95Domains1 = expandDomains root8Node95Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node95Domains1 v = expandDomains root8Node95Domains1Fast v from by decide) v
theorem root8Node95Step1Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root8Node95Domains0 root8Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node95Domains0 root8Node95Domains1
    root8Node95Domains0Fast root8Node95Domains1Fast
    root8Node95Domains0_fast_eq root8Node95Domains1_fast_eq (by decide)
theorem root8Node95Step1_checked :
    checkReplacement table23 root8Node95Domains0 root8Node95Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node95Step1Chunk0_0_checked, root8Node95Step1Chunk0_1_checked, root8Node95Step1Chunk0_2_checked, root8Node95Step1Chunk0_3_checked, root8Node95Step1Chunk0_4_checked, root8Node95Step1Chunk0_5_checked, root8Node95Step1Chunk1_0_checked, root8Node95Step1Chunk1_1_checked, root8Node95Step1Chunk1_2_checked, root8Node95Step1Chunk1_3_checked, root8Node95Step1Chunk1_4_checked, root8Node95Step1Chunk1_5_checked, root8Node95Step1Chunk2_0_checked, root8Node95Step1Chunk2_1_checked, root8Node95Step1Chunk2_2_checked, root8Node95Step1Chunk2_3_checked, root8Node95Step1Chunk2_4_checked, root8Node95Step1Chunk2_5_checked, root8Node95Step1Chunk3_0_checked, root8Node95Step1Chunk3_1_checked, root8Node95Step1Chunk3_2_checked, root8Node95Step1Chunk3_3_checked, root8Node95Step1Chunk3_4_checked, root8Node95Step1Chunk3_5_checked, root8Node95Step1Chunk4_0_checked, root8Node95Step1Chunk4_1_checked, root8Node95Step1Chunk4_2_checked, root8Node95Step1Chunk4_3_checked, root8Node95Step1Chunk4_4_checked, root8Node95Step1Chunk4_5_checked, root8Node95Step1Chunk5_0_checked, root8Node95Step1Chunk5_1_checked, root8Node95Step1Chunk5_2_checked, root8Node95Step1Chunk5_3_checked, root8Node95Step1Chunk5_4_checked, root8Node95Step1Chunk5_5_checked, root8Node95Step1Chunk6_0_checked, root8Node95Step1Chunk6_1_checked, root8Node95Step1Chunk6_2_checked, root8Node95Step1Chunk6_3_checked, root8Node95Step1Chunk6_4_checked, root8Node95Step1Chunk6_5_checked, root8Node95Step1Chunk7_0_checked, root8Node95Step1Chunk7_1_checked, root8Node95Step1Chunk7_2_checked, root8Node95Step1Chunk7_3_checked, root8Node95Step1Chunk7_4_checked, root8Node95Step1Chunk7_5_checked, root8Node95Step1Chunk8_0_checked, root8Node95Step1Chunk8_1_checked, root8Node95Step1Chunk8_2_checked, root8Node95Step1Chunk8_3_checked, root8Node95Step1Chunk8_4_checked, root8Node95Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node96Domains0 : Domains 61 State := restrict root8Node95Domains1 50 (7,2)
def root8Node96Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(2,3)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3)]
  | 25 => some [(5,1)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(7,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,1),(5,4)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root8Node96Domains0_fast_eq : root8Node96Domains0 = expandDomains root8Node96Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node96Domains0 v = expandDomains root8Node96Domains0Fast v from by decide) v
def root8Node96Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(5,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(2,3)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(6,4)]
  | 17 => [(1,2)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3)]
  | 25 => [(5,1)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2)]
  | 33 => [(5,3)]
  | 34 => [(8,5)]
  | 35 => [(5,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(7,4)]
  | 42 => [(1,3)]
  | 43 => [(8,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(0,3)]
  | 48 => [(8,1)]
  | 49 => [(6,5)]
  | 50 => [(7,2)]
  | 51 => [(4,0)]
  | 52 => [(7,3)]
  | 53 => [(4,2)]
  | 54 => [(5,3)]
  | 55 => [(8,5)]
  | 56 => [(5,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(7,4)]
  | _ => [(6,3)]
def root8Node96Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(2,3)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3)]
  | 25 => some [(5,1)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(7,2)]
  | 51 => some [(4,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root8Node96Domains1_fast_eq : root8Node96Domains1 = expandDomains root8Node96Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node96Domains1 v = expandDomains root8Node96Domains1Fast v from by decide) v
theorem root8Node96Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root8Node96Domains0 root8Node96Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node96Domains0 root8Node96Domains1
    root8Node96Domains0Fast root8Node96Domains1Fast
    root8Node96Domains0_fast_eq root8Node96Domains1_fast_eq (by decide)
theorem root8Node96Step1_checked :
    checkReplacement table37 root8Node96Domains0 root8Node96Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node96Step1Chunk0_0_checked, root8Node96Step1Chunk0_1_checked, root8Node96Step1Chunk0_2_checked, root8Node96Step1Chunk0_3_checked, root8Node96Step1Chunk0_4_checked, root8Node96Step1Chunk0_5_checked, root8Node96Step1Chunk1_0_checked, root8Node96Step1Chunk1_1_checked, root8Node96Step1Chunk1_2_checked, root8Node96Step1Chunk1_3_checked, root8Node96Step1Chunk1_4_checked, root8Node96Step1Chunk1_5_checked, root8Node96Step1Chunk2_0_checked, root8Node96Step1Chunk2_1_checked, root8Node96Step1Chunk2_2_checked, root8Node96Step1Chunk2_3_checked, root8Node96Step1Chunk2_4_checked, root8Node96Step1Chunk2_5_checked, root8Node96Step1Chunk3_0_checked, root8Node96Step1Chunk3_1_checked, root8Node96Step1Chunk3_2_checked, root8Node96Step1Chunk3_3_checked, root8Node96Step1Chunk3_4_checked, root8Node96Step1Chunk3_5_checked, root8Node96Step1Chunk4_0_checked, root8Node96Step1Chunk4_1_checked, root8Node96Step1Chunk4_2_checked, root8Node96Step1Chunk4_3_checked, root8Node96Step1Chunk4_4_checked, root8Node96Step1Chunk4_5_checked, root8Node96Step1Chunk5_0_checked, root8Node96Step1Chunk5_1_checked, root8Node96Step1Chunk5_2_checked, root8Node96Step1Chunk5_3_checked, root8Node96Step1Chunk5_4_checked, root8Node96Step1Chunk5_5_checked, root8Node96Step1Chunk6_0_checked, root8Node96Step1Chunk6_1_checked, root8Node96Step1Chunk6_2_checked, root8Node96Step1Chunk6_3_checked, root8Node96Step1Chunk6_4_checked, root8Node96Step1Chunk6_5_checked, root8Node96Step1Chunk7_0_checked, root8Node96Step1Chunk7_1_checked, root8Node96Step1Chunk7_2_checked, root8Node96Step1Chunk7_3_checked, root8Node96Step1Chunk7_4_checked, root8Node96Step1Chunk7_5_checked, root8Node96Step1Chunk8_0_checked, root8Node96Step1Chunk8_1_checked, root8Node96Step1Chunk8_2_checked, root8Node96Step1Chunk8_3_checked, root8Node96Step1Chunk8_4_checked, root8Node96Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node96Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node96Domains1 (.output 47) = true := by decide
def root8Node97Domains0 : Domains 61 State := restrict root8Node95Domains1 50 (8,2)
def root8Node97Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(2,3)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3)]
  | 25 => some [(5,1)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,1),(5,4)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root8Node97Domains0_fast_eq : root8Node97Domains0 = expandDomains root8Node97Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node97Domains0 v = expandDomains root8Node97Domains0Fast v from by decide) v
def root8Node97Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(5,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(2,3)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(6,4)]
  | 17 => [(1,2)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3)]
  | 25 => [(5,1)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2)]
  | 33 => [(5,3)]
  | 34 => [(8,5)]
  | 35 => [(5,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(7,4)]
  | 42 => [(1,3)]
  | 43 => [(8,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(0,3)]
  | 48 => [(8,1)]
  | 49 => [(6,5)]
  | 50 => [(8,2)]
  | 51 => [(8,0)]
  | 52 => [(7,3)]
  | 53 => [(4,2)]
  | 54 => [(5,3)]
  | 55 => [(8,5)]
  | 56 => [(5,4)]
  | 57 => [(6,4)]
  | 58 => [(1,2)]
  | 59 => [(7,4)]
  | _ => [(6,3)]
def root8Node97Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(2,3)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3)]
  | 25 => some [(5,1)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(8,2)]
  | 51 => some [(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,4)]
  | 57 => some [(6,4)]
  | 58 => some [(1,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root8Node97Domains1_fast_eq : root8Node97Domains1 = expandDomains root8Node97Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node97Domains1 v = expandDomains root8Node97Domains1Fast v from by decide) v
theorem root8Node97Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root8Node97Domains0 root8Node97Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node97Domains0 root8Node97Domains1
    root8Node97Domains0Fast root8Node97Domains1Fast
    root8Node97Domains0_fast_eq root8Node97Domains1_fast_eq (by decide)
theorem root8Node97Step1_checked :
    checkReplacement table37 root8Node97Domains0 root8Node97Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node97Step1Chunk0_0_checked, root8Node97Step1Chunk0_1_checked, root8Node97Step1Chunk0_2_checked, root8Node97Step1Chunk0_3_checked, root8Node97Step1Chunk0_4_checked, root8Node97Step1Chunk0_5_checked, root8Node97Step1Chunk1_0_checked, root8Node97Step1Chunk1_1_checked, root8Node97Step1Chunk1_2_checked, root8Node97Step1Chunk1_3_checked, root8Node97Step1Chunk1_4_checked, root8Node97Step1Chunk1_5_checked, root8Node97Step1Chunk2_0_checked, root8Node97Step1Chunk2_1_checked, root8Node97Step1Chunk2_2_checked, root8Node97Step1Chunk2_3_checked, root8Node97Step1Chunk2_4_checked, root8Node97Step1Chunk2_5_checked, root8Node97Step1Chunk3_0_checked, root8Node97Step1Chunk3_1_checked, root8Node97Step1Chunk3_2_checked, root8Node97Step1Chunk3_3_checked, root8Node97Step1Chunk3_4_checked, root8Node97Step1Chunk3_5_checked, root8Node97Step1Chunk4_0_checked, root8Node97Step1Chunk4_1_checked, root8Node97Step1Chunk4_2_checked, root8Node97Step1Chunk4_3_checked, root8Node97Step1Chunk4_4_checked, root8Node97Step1Chunk4_5_checked, root8Node97Step1Chunk5_0_checked, root8Node97Step1Chunk5_1_checked, root8Node97Step1Chunk5_2_checked, root8Node97Step1Chunk5_3_checked, root8Node97Step1Chunk5_4_checked, root8Node97Step1Chunk5_5_checked, root8Node97Step1Chunk6_0_checked, root8Node97Step1Chunk6_1_checked, root8Node97Step1Chunk6_2_checked, root8Node97Step1Chunk6_3_checked, root8Node97Step1Chunk6_4_checked, root8Node97Step1Chunk6_5_checked, root8Node97Step1Chunk7_0_checked, root8Node97Step1Chunk7_1_checked, root8Node97Step1Chunk7_2_checked, root8Node97Step1Chunk7_3_checked, root8Node97Step1Chunk7_4_checked, root8Node97Step1Chunk7_5_checked, root8Node97Step1Chunk8_0_checked, root8Node97Step1Chunk8_1_checked, root8Node97Step1Chunk8_2_checked, root8Node97Step1Chunk8_3_checked, root8Node97Step1Chunk8_4_checked, root8Node97Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node97Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node97Domains1 (.output 48) = true := by decide
def root8Node98Domains0 : Domains 61 State := restrict root8Node94Domains3 10 (4,3)
def root8Node98Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(3,1),(5,1),(7,1)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(8,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(1,3)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(1,5),(6,5)]
  | 50 => some [(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,1),(5,4)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root8Node98Domains0_fast_eq : root8Node98Domains0 = expandDomains root8Node98Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node98Domains0 v = expandDomains root8Node98Domains0Fast v from by decide) v
def root8Node98Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(5,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(1,4)]
  | 17 => [(0,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(3,1),(7,1)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(8,2)]
  | 33 => [(5,0)]
  | 34 => [(4,5)]
  | 35 => [(5,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(8,4)]
  | 42 => [(0,0)]
  | 43 => [(8,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(0,3)]
  | 48 => [(8,1)]
  | 49 => [(1,5)]
  | 50 => [(7,2),(8,2)]
  | 51 => [(4,0),(8,0)]
  | 52 => [(7,3)]
  | 53 => [(4,2)]
  | 54 => [(5,3)]
  | 55 => [(8,5)]
  | 56 => [(5,1),(5,4)]
  | 57 => [(0,1),(6,4)]
  | 58 => [(1,2),(6,2)]
  | 59 => [(7,4)]
  | _ => [(6,3)]
def root8Node98Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(3,1),(7,1)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(8,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(1,5)]
  | 50 => some [(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,1),(5,4)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root8Node98Domains1_fast_eq : root8Node98Domains1 = expandDomains root8Node98Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node98Domains1 v = expandDomains root8Node98Domains1Fast v from by decide) v
theorem root8Node98Step1Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1_checked :
    checkReplacement table23 root8Node98Domains0 root8Node98Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node98Step1Chunk0_0_checked, root8Node98Step1Chunk0_1_checked, root8Node98Step1Chunk0_2_checked, root8Node98Step1Chunk0_3_checked, root8Node98Step1Chunk0_4_checked, root8Node98Step1Chunk0_5_checked, root8Node98Step1Chunk1_0_checked, root8Node98Step1Chunk1_1_checked, root8Node98Step1Chunk1_2_checked, root8Node98Step1Chunk1_3_checked, root8Node98Step1Chunk1_4_checked, root8Node98Step1Chunk1_5_checked, root8Node98Step1Chunk2_0_checked, root8Node98Step1Chunk2_1_checked, root8Node98Step1Chunk2_2_checked, root8Node98Step1Chunk2_3_checked, root8Node98Step1Chunk2_4_checked, root8Node98Step1Chunk2_5_checked, root8Node98Step1Chunk3_0_checked, root8Node98Step1Chunk3_1_checked, root8Node98Step1Chunk3_2_checked, root8Node98Step1Chunk3_3_checked, root8Node98Step1Chunk3_4_checked, root8Node98Step1Chunk3_5_checked, root8Node98Step1Chunk4_0_checked, root8Node98Step1Chunk4_1_checked, root8Node98Step1Chunk4_2_checked, root8Node98Step1Chunk4_3_checked, root8Node98Step1Chunk4_4_checked, root8Node98Step1Chunk4_5_checked, root8Node98Step1Chunk5_0_checked, root8Node98Step1Chunk5_1_checked, root8Node98Step1Chunk5_2_checked, root8Node98Step1Chunk5_3_checked, root8Node98Step1Chunk5_4_checked, root8Node98Step1Chunk5_5_checked, root8Node98Step1Chunk6_0_checked, root8Node98Step1Chunk6_1_checked, root8Node98Step1Chunk6_2_checked, root8Node98Step1Chunk6_3_checked, root8Node98Step1Chunk6_4_checked, root8Node98Step1Chunk6_5_checked, root8Node98Step1Chunk7_0_checked, root8Node98Step1Chunk7_1_checked, root8Node98Step1Chunk7_2_checked, root8Node98Step1Chunk7_3_checked, root8Node98Step1Chunk7_4_checked, root8Node98Step1Chunk7_5_checked, root8Node98Step1Chunk8_0_checked, root8Node98Step1Chunk8_1_checked, root8Node98Step1Chunk8_2_checked, root8Node98Step1Chunk8_3_checked, root8Node98Step1Chunk8_4_checked, root8Node98Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
