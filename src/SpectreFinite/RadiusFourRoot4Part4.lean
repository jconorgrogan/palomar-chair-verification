module

public import SpectreFinite.RadiusFourRoot4Part3
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable16
public import SpectreFinite.RadiusFourTable39
public import SpectreFinite.RadiusFourTable40
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node9Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(1,5)]
  | 4 => [(6,1)]
  | 5 => [(1,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(3,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(5,5)]
  | 19 => [(7,0)]
  | 20 => [(2,3)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(6,4)]
  | 29 => [(1,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(8,0)]
  | 34 => [(7,3),(8,3)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(1,4),(6,4)]
  | 43 => [(7,3)]
  | 44 => [(4,2)]
  | 45 => [(5,3)]
  | 46 => [(8,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(1,2)]
  | 51 => [(7,4)]
  | 52 => [(1,3),(6,3)]
  | 53 => [(7,2),(8,2)]
  | 54 => [(4,0),(8,0)]
  | 55 => [(7,3)]
  | 56 => [(4,1),(8,1)]
  | 57 => [(0,2),(6,5)]
  | 58 => [(0,4),(1,1)]
  | 59 => [(5,1),(5,4)]
  | _ => [(0,1),(6,4)]
def root4Node9Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(1,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(3,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(7,0)]
  | 20 => some [(2,3)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(6,4)]
  | 29 => some [(1,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(7,3),(8,3)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(1,4),(6,4)]
  | 43 => some [(7,3)]
  | 44 => some [(4,2)]
  | 45 => some [(5,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(1,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3),(6,3)]
  | 53 => some [(7,2),(8,2)]
  | 54 => some [(4,0),(8,0)]
  | 55 => some [(7,3)]
  | 56 => some [(4,1),(8,1)]
  | 57 => some [(0,2),(6,5)]
  | 58 => some [(0,4),(1,1)]
  | 59 => some [(5,1),(5,4)]
  | _ => some [(0,1),(6,4)]
theorem root4Node9Domains3_fast_eq : root4Node9Domains3 = expandDomains root4Node9Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node9Domains3 v = expandDomains root4Node9Domains3Fast v from by decide) v
theorem root4Node9Step3Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root4Node9Domains2 root4Node9Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node9Domains2 root4Node9Domains3
    root4Node9Domains2Fast root4Node9Domains3Fast
    root4Node9Domains2_fast_eq root4Node9Domains3_fast_eq (by decide)
theorem root4Node9Step3_checked :
    checkReplacement table39 root4Node9Domains2 root4Node9Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node9Step3Chunk0_0_checked, root4Node9Step3Chunk0_1_checked, root4Node9Step3Chunk0_2_checked, root4Node9Step3Chunk0_3_checked, root4Node9Step3Chunk0_4_checked, root4Node9Step3Chunk0_5_checked, root4Node9Step3Chunk1_0_checked, root4Node9Step3Chunk1_1_checked, root4Node9Step3Chunk1_2_checked, root4Node9Step3Chunk1_3_checked, root4Node9Step3Chunk1_4_checked, root4Node9Step3Chunk1_5_checked, root4Node9Step3Chunk2_0_checked, root4Node9Step3Chunk2_1_checked, root4Node9Step3Chunk2_2_checked, root4Node9Step3Chunk2_3_checked, root4Node9Step3Chunk2_4_checked, root4Node9Step3Chunk2_5_checked, root4Node9Step3Chunk3_0_checked, root4Node9Step3Chunk3_1_checked, root4Node9Step3Chunk3_2_checked, root4Node9Step3Chunk3_3_checked, root4Node9Step3Chunk3_4_checked, root4Node9Step3Chunk3_5_checked, root4Node9Step3Chunk4_0_checked, root4Node9Step3Chunk4_1_checked, root4Node9Step3Chunk4_2_checked, root4Node9Step3Chunk4_3_checked, root4Node9Step3Chunk4_4_checked, root4Node9Step3Chunk4_5_checked, root4Node9Step3Chunk5_0_checked, root4Node9Step3Chunk5_1_checked, root4Node9Step3Chunk5_2_checked, root4Node9Step3Chunk5_3_checked, root4Node9Step3Chunk5_4_checked, root4Node9Step3Chunk5_5_checked, root4Node9Step3Chunk6_0_checked, root4Node9Step3Chunk6_1_checked, root4Node9Step3Chunk6_2_checked, root4Node9Step3Chunk6_3_checked, root4Node9Step3Chunk6_4_checked, root4Node9Step3Chunk6_5_checked, root4Node9Step3Chunk7_0_checked, root4Node9Step3Chunk7_1_checked, root4Node9Step3Chunk7_2_checked, root4Node9Step3Chunk7_3_checked, root4Node9Step3Chunk7_4_checked, root4Node9Step3Chunk7_5_checked, root4Node9Step3Chunk8_0_checked, root4Node9Step3Chunk8_1_checked, root4Node9Step3Chunk8_2_checked, root4Node9Step3Chunk8_3_checked, root4Node9Step3Chunk8_4_checked, root4Node9Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node10Domains0 : Domains 61 State := restrict root4Node9Domains3 34 (7,3)
def root4Node10Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(1,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(3,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(7,0)]
  | 20 => some [(2,3)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(6,4)]
  | 29 => some [(1,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(1,4),(6,4)]
  | 43 => some [(7,3)]
  | 44 => some [(4,2)]
  | 45 => some [(5,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(1,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3),(6,3)]
  | 53 => some [(7,2),(8,2)]
  | 54 => some [(4,0),(8,0)]
  | 55 => some [(7,3)]
  | 56 => some [(4,1),(8,1)]
  | 57 => some [(0,2),(6,5)]
  | 58 => some [(0,4),(1,1)]
  | 59 => some [(5,1),(5,4)]
  | _ => some [(0,1),(6,4)]
theorem root4Node10Domains0_fast_eq : root4Node10Domains0 = expandDomains root4Node10Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node10Domains0 v = expandDomains root4Node10Domains0Fast v from by decide) v
def root4Node10Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(1,5)]
  | 4 => [(6,1)]
  | 5 => [(1,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(3,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(5,5)]
  | 19 => [(7,0)]
  | 20 => [(2,3)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(6,4)]
  | 29 => [(1,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(8,0)]
  | 34 => [(7,3)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(6,4)]
  | 43 => [(7,3)]
  | 44 => [(4,2)]
  | 45 => [(5,3)]
  | 46 => [(8,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(1,2)]
  | 51 => [(7,4)]
  | 52 => [(1,3),(6,3)]
  | 53 => [(7,2),(8,2)]
  | 54 => [(4,0),(8,0)]
  | 55 => [(7,3)]
  | 56 => [(4,1),(8,1)]
  | 57 => [(0,2),(6,5)]
  | 58 => [(0,4),(1,1)]
  | 59 => [(5,1),(5,4)]
  | _ => [(0,1),(6,4)]
def root4Node10Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(1,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(3,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(7,0)]
  | 20 => some [(2,3)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(6,4)]
  | 29 => some [(1,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(6,4)]
  | 43 => some [(7,3)]
  | 44 => some [(4,2)]
  | 45 => some [(5,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(1,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3),(6,3)]
  | 53 => some [(7,2),(8,2)]
  | 54 => some [(4,0),(8,0)]
  | 55 => some [(7,3)]
  | 56 => some [(4,1),(8,1)]
  | 57 => some [(0,2),(6,5)]
  | 58 => some [(0,4),(1,1)]
  | 59 => some [(5,1),(5,4)]
  | _ => some [(0,1),(6,4)]
theorem root4Node10Domains1_fast_eq : root4Node10Domains1 = expandDomains root4Node10Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node10Domains1 v = expandDomains root4Node10Domains1Fast v from by decide) v
theorem root4Node10Step1Chunk0_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_0⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk0_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_1⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk0_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_2⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk0_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_3⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk0_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_4⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk0_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_5⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk1_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_0⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk1_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_1⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk1_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_2⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk1_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_3⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk1_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_4⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk1_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_5⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk2_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_0⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk2_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_1⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk2_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_2⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk2_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_3⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk2_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_4⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk2_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_5⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk3_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_0⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk3_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_1⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk3_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_2⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk3_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_3⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk3_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_4⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk3_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_5⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk4_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_0⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk4_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_1⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk4_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_2⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk4_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_3⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk4_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_4⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk4_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_5⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk5_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_0⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk5_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_1⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk5_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_2⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk5_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_3⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk5_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_4⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk5_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_5⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk6_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_0⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk6_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_1⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk6_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_2⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk6_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_3⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk6_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_4⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk6_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_5⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk7_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_0⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk7_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_1⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk7_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_2⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk7_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_3⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk7_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_4⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk7_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_5⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk8_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_0⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk8_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_1⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk8_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_2⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk8_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_3⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk8_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_4⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1Chunk8_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_5⟩
      root4Node10Domains0 root4Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node10Domains0 root4Node10Domains1
    root4Node10Domains0Fast root4Node10Domains1Fast
    root4Node10Domains0_fast_eq root4Node10Domains1_fast_eq (by decide)
theorem root4Node10Step1_checked :
    checkReplacement table16 root4Node10Domains0 root4Node10Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node10Step1Chunk0_0_checked, root4Node10Step1Chunk0_1_checked, root4Node10Step1Chunk0_2_checked, root4Node10Step1Chunk0_3_checked, root4Node10Step1Chunk0_4_checked, root4Node10Step1Chunk0_5_checked, root4Node10Step1Chunk1_0_checked, root4Node10Step1Chunk1_1_checked, root4Node10Step1Chunk1_2_checked, root4Node10Step1Chunk1_3_checked, root4Node10Step1Chunk1_4_checked, root4Node10Step1Chunk1_5_checked, root4Node10Step1Chunk2_0_checked, root4Node10Step1Chunk2_1_checked, root4Node10Step1Chunk2_2_checked, root4Node10Step1Chunk2_3_checked, root4Node10Step1Chunk2_4_checked, root4Node10Step1Chunk2_5_checked, root4Node10Step1Chunk3_0_checked, root4Node10Step1Chunk3_1_checked, root4Node10Step1Chunk3_2_checked, root4Node10Step1Chunk3_3_checked, root4Node10Step1Chunk3_4_checked, root4Node10Step1Chunk3_5_checked, root4Node10Step1Chunk4_0_checked, root4Node10Step1Chunk4_1_checked, root4Node10Step1Chunk4_2_checked, root4Node10Step1Chunk4_3_checked, root4Node10Step1Chunk4_4_checked, root4Node10Step1Chunk4_5_checked, root4Node10Step1Chunk5_0_checked, root4Node10Step1Chunk5_1_checked, root4Node10Step1Chunk5_2_checked, root4Node10Step1Chunk5_3_checked, root4Node10Step1Chunk5_4_checked, root4Node10Step1Chunk5_5_checked, root4Node10Step1Chunk6_0_checked, root4Node10Step1Chunk6_1_checked, root4Node10Step1Chunk6_2_checked, root4Node10Step1Chunk6_3_checked, root4Node10Step1Chunk6_4_checked, root4Node10Step1Chunk6_5_checked, root4Node10Step1Chunk7_0_checked, root4Node10Step1Chunk7_1_checked, root4Node10Step1Chunk7_2_checked, root4Node10Step1Chunk7_3_checked, root4Node10Step1Chunk7_4_checked, root4Node10Step1Chunk7_5_checked, root4Node10Step1Chunk8_0_checked, root4Node10Step1Chunk8_1_checked, root4Node10Step1Chunk8_2_checked, root4Node10Step1Chunk8_3_checked, root4Node10Step1Chunk8_4_checked, root4Node10Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node11Domains0 : Domains 61 State := restrict root4Node10Domains1 52 (1,3)
def root4Node11Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(1,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(3,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(7,0)]
  | 20 => some [(2,3)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(6,4)]
  | 29 => some [(1,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(6,4)]
  | 43 => some [(7,3)]
  | 44 => some [(4,2)]
  | 45 => some [(5,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(1,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3)]
  | 53 => some [(7,2),(8,2)]
  | 54 => some [(4,0),(8,0)]
  | 55 => some [(7,3)]
  | 56 => some [(4,1),(8,1)]
  | 57 => some [(0,2),(6,5)]
  | 58 => some [(0,4),(1,1)]
  | 59 => some [(5,1),(5,4)]
  | _ => some [(0,1),(6,4)]
theorem root4Node11Domains0_fast_eq : root4Node11Domains0 = expandDomains root4Node11Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node11Domains0 v = expandDomains root4Node11Domains0Fast v from by decide) v
def root4Node11Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(1,5)]
  | 4 => [(6,1)]
  | 5 => [(1,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(3,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(5,5)]
  | 19 => [(7,0)]
  | 20 => [(2,3)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(6,4)]
  | 29 => [(1,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(8,0)]
  | 34 => [(7,3)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(6,4)]
  | 43 => [(7,3)]
  | 44 => [(4,2)]
  | 45 => [(5,3)]
  | 46 => [(8,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(1,2)]
  | 51 => [(7,4)]
  | 52 => [(1,3)]
  | 53 => [(8,2)]
  | 54 => [(8,0)]
  | 55 => [(7,3)]
  | 56 => [(8,1)]
  | 57 => [(6,5)]
  | 58 => [(0,4)]
  | 59 => [(5,4)]
  | _ => [(6,4)]
def root4Node11Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(1,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(3,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(7,0)]
  | 20 => some [(2,3)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(6,4)]
  | 29 => some [(1,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(6,4)]
  | 43 => some [(7,3)]
  | 44 => some [(4,2)]
  | 45 => some [(5,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(1,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3)]
  | 53 => some [(8,2)]
  | 54 => some [(8,0)]
  | 55 => some [(7,3)]
  | 56 => some [(8,1)]
  | 57 => some [(6,5)]
  | 58 => some [(0,4)]
  | 59 => some [(5,4)]
  | _ => some [(6,4)]
theorem root4Node11Domains1_fast_eq : root4Node11Domains1 = expandDomains root4Node11Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node11Domains1 v = expandDomains root4Node11Domains1Fast v from by decide) v
theorem root4Node11Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root4Node11Domains0 root4Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node11Domains0 root4Node11Domains1
    root4Node11Domains0Fast root4Node11Domains1Fast
    root4Node11Domains0_fast_eq root4Node11Domains1_fast_eq (by decide)
theorem root4Node11Step1_checked :
    checkReplacement table46 root4Node11Domains0 root4Node11Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node11Step1Chunk0_0_checked, root4Node11Step1Chunk0_1_checked, root4Node11Step1Chunk0_2_checked, root4Node11Step1Chunk0_3_checked, root4Node11Step1Chunk0_4_checked, root4Node11Step1Chunk0_5_checked, root4Node11Step1Chunk1_0_checked, root4Node11Step1Chunk1_1_checked, root4Node11Step1Chunk1_2_checked, root4Node11Step1Chunk1_3_checked, root4Node11Step1Chunk1_4_checked, root4Node11Step1Chunk1_5_checked, root4Node11Step1Chunk2_0_checked, root4Node11Step1Chunk2_1_checked, root4Node11Step1Chunk2_2_checked, root4Node11Step1Chunk2_3_checked, root4Node11Step1Chunk2_4_checked, root4Node11Step1Chunk2_5_checked, root4Node11Step1Chunk3_0_checked, root4Node11Step1Chunk3_1_checked, root4Node11Step1Chunk3_2_checked, root4Node11Step1Chunk3_3_checked, root4Node11Step1Chunk3_4_checked, root4Node11Step1Chunk3_5_checked, root4Node11Step1Chunk4_0_checked, root4Node11Step1Chunk4_1_checked, root4Node11Step1Chunk4_2_checked, root4Node11Step1Chunk4_3_checked, root4Node11Step1Chunk4_4_checked, root4Node11Step1Chunk4_5_checked, root4Node11Step1Chunk5_0_checked, root4Node11Step1Chunk5_1_checked, root4Node11Step1Chunk5_2_checked, root4Node11Step1Chunk5_3_checked, root4Node11Step1Chunk5_4_checked, root4Node11Step1Chunk5_5_checked, root4Node11Step1Chunk6_0_checked, root4Node11Step1Chunk6_1_checked, root4Node11Step1Chunk6_2_checked, root4Node11Step1Chunk6_3_checked, root4Node11Step1Chunk6_4_checked, root4Node11Step1Chunk6_5_checked, root4Node11Step1Chunk7_0_checked, root4Node11Step1Chunk7_1_checked, root4Node11Step1Chunk7_2_checked, root4Node11Step1Chunk7_3_checked, root4Node11Step1Chunk7_4_checked, root4Node11Step1Chunk7_5_checked, root4Node11Step1Chunk8_0_checked, root4Node11Step1Chunk8_1_checked, root4Node11Step1Chunk8_2_checked, root4Node11Step1Chunk8_3_checked, root4Node11Step1Chunk8_4_checked, root4Node11Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root4Node11Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node11Domains1 (.output 3) = true := by decide
def root4Node12Domains0 : Domains 61 State := restrict root4Node10Domains1 52 (6,3)
def root4Node12Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(1,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(3,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(7,0)]
  | 20 => some [(2,3)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(6,4)]
  | 29 => some [(1,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(6,4)]
  | 43 => some [(7,3)]
  | 44 => some [(4,2)]
  | 45 => some [(5,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(1,2)]
  | 51 => some [(7,4)]
  | 52 => some [(6,3)]
  | 53 => some [(7,2),(8,2)]
  | 54 => some [(4,0),(8,0)]
  | 55 => some [(7,3)]
  | 56 => some [(4,1),(8,1)]
  | 57 => some [(0,2),(6,5)]
  | 58 => some [(0,4),(1,1)]
  | 59 => some [(5,1),(5,4)]
  | _ => some [(0,1),(6,4)]
theorem root4Node12Domains0_fast_eq : root4Node12Domains0 = expandDomains root4Node12Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node12Domains0 v = expandDomains root4Node12Domains0Fast v from by decide) v
def root4Node12Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(1,5)]
  | 4 => [(6,1)]
  | 5 => [(1,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(3,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(5,5)]
  | 19 => [(7,0)]
  | 20 => [(2,3)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(6,4)]
  | 29 => [(1,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(8,0)]
  | 34 => [(7,3)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(6,4)]
  | 43 => [(7,3)]
  | 44 => [(4,2)]
  | 45 => [(5,3)]
  | 46 => [(8,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(1,2)]
  | 51 => [(7,4)]
  | 52 => [(6,3)]
  | 53 => [(7,2)]
  | 54 => [(4,0)]
  | 55 => [(7,3)]
  | 56 => [(4,1)]
  | 57 => [(0,2)]
  | 58 => [(1,1)]
  | 59 => [(5,1)]
  | _ => [(0,1)]
def root4Node12Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(1,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(3,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(7,0)]
  | 20 => some [(2,3)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(6,4)]
  | 29 => some [(1,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(6,4)]
  | 43 => some [(7,3)]
  | 44 => some [(4,2)]
  | 45 => some [(5,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(1,2)]
  | 51 => some [(7,4)]
  | 52 => some [(6,3)]
  | 53 => some [(7,2)]
  | 54 => some [(4,0)]
  | 55 => some [(7,3)]
  | 56 => some [(4,1)]
  | 57 => some [(0,2)]
  | 58 => some [(1,1)]
  | 59 => some [(5,1)]
  | _ => some [(0,1)]
theorem root4Node12Domains1_fast_eq : root4Node12Domains1 = expandDomains root4Node12Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node12Domains1 v = expandDomains root4Node12Domains1Fast v from by decide) v
theorem root4Node12Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root4Node12Domains0 root4Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node12Domains0 root4Node12Domains1
    root4Node12Domains0Fast root4Node12Domains1Fast
    root4Node12Domains0_fast_eq root4Node12Domains1_fast_eq (by decide)
theorem root4Node12Step1_checked :
    checkReplacement table46 root4Node12Domains0 root4Node12Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node12Step1Chunk0_0_checked, root4Node12Step1Chunk0_1_checked, root4Node12Step1Chunk0_2_checked, root4Node12Step1Chunk0_3_checked, root4Node12Step1Chunk0_4_checked, root4Node12Step1Chunk0_5_checked, root4Node12Step1Chunk1_0_checked, root4Node12Step1Chunk1_1_checked, root4Node12Step1Chunk1_2_checked, root4Node12Step1Chunk1_3_checked, root4Node12Step1Chunk1_4_checked, root4Node12Step1Chunk1_5_checked, root4Node12Step1Chunk2_0_checked, root4Node12Step1Chunk2_1_checked, root4Node12Step1Chunk2_2_checked, root4Node12Step1Chunk2_3_checked, root4Node12Step1Chunk2_4_checked, root4Node12Step1Chunk2_5_checked, root4Node12Step1Chunk3_0_checked, root4Node12Step1Chunk3_1_checked, root4Node12Step1Chunk3_2_checked, root4Node12Step1Chunk3_3_checked, root4Node12Step1Chunk3_4_checked, root4Node12Step1Chunk3_5_checked, root4Node12Step1Chunk4_0_checked, root4Node12Step1Chunk4_1_checked, root4Node12Step1Chunk4_2_checked, root4Node12Step1Chunk4_3_checked, root4Node12Step1Chunk4_4_checked, root4Node12Step1Chunk4_5_checked, root4Node12Step1Chunk5_0_checked, root4Node12Step1Chunk5_1_checked, root4Node12Step1Chunk5_2_checked, root4Node12Step1Chunk5_3_checked, root4Node12Step1Chunk5_4_checked, root4Node12Step1Chunk5_5_checked, root4Node12Step1Chunk6_0_checked, root4Node12Step1Chunk6_1_checked, root4Node12Step1Chunk6_2_checked, root4Node12Step1Chunk6_3_checked, root4Node12Step1Chunk6_4_checked, root4Node12Step1Chunk6_5_checked, root4Node12Step1Chunk7_0_checked, root4Node12Step1Chunk7_1_checked, root4Node12Step1Chunk7_2_checked, root4Node12Step1Chunk7_3_checked, root4Node12Step1Chunk7_4_checked, root4Node12Step1Chunk7_5_checked, root4Node12Step1Chunk8_0_checked, root4Node12Step1Chunk8_1_checked, root4Node12Step1Chunk8_2_checked, root4Node12Step1Chunk8_3_checked, root4Node12Step1Chunk8_4_checked, root4Node12Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root4Node12Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node12Domains1 (.output 4) = true := by decide
def root4Node13Domains0 : Domains 61 State := restrict root4Node9Domains3 34 (8,3)
def root4Node13Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(1,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(3,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(7,0)]
  | 20 => some [(2,3)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(6,4)]
  | 29 => some [(1,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(8,3)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(1,4),(6,4)]
  | 43 => some [(7,3)]
  | 44 => some [(4,2)]
  | 45 => some [(5,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(1,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3),(6,3)]
  | 53 => some [(7,2),(8,2)]
  | 54 => some [(4,0),(8,0)]
  | 55 => some [(7,3)]
  | 56 => some [(4,1),(8,1)]
  | 57 => some [(0,2),(6,5)]
  | 58 => some [(0,4),(1,1)]
  | 59 => some [(5,1),(5,4)]
  | _ => some [(0,1),(6,4)]
theorem root4Node13Domains0_fast_eq : root4Node13Domains0 = expandDomains root4Node13Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node13Domains0 v = expandDomains root4Node13Domains0Fast v from by decide) v
def root4Node13Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(1,5)]
  | 4 => [(6,1)]
  | 5 => [(1,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(6,5)]
  | 12 => [(0,4)]
  | 13 => [(3,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(5,5)]
  | 19 => [(7,0)]
  | 20 => [(2,3)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(6,4)]
  | 29 => [(1,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(8,0)]
  | 34 => [(8,3)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(1,4)]
  | 43 => [(7,3)]
  | 44 => [(4,2)]
  | 45 => [(5,3)]
  | 46 => [(8,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(1,2)]
  | 51 => [(7,4)]
  | 52 => [(1,3)]
  | 53 => [(8,2)]
  | 54 => [(8,0)]
  | 55 => [(7,3)]
  | 56 => [(4,1),(8,1)]
  | 57 => [(0,2),(6,5)]
  | 58 => [(0,4)]
  | 59 => [(5,4)]
  | _ => [(6,4)]
def root4Node13Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(1,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,5)]
  | 12 => some [(0,4)]
  | 13 => some [(3,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(7,0)]
  | 20 => some [(2,3)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(6,4)]
  | 29 => some [(1,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(8,3)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(7,3)]
  | 44 => some [(4,2)]
  | 45 => some [(5,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(1,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3)]
  | 53 => some [(8,2)]
  | 54 => some [(8,0)]
  | 55 => some [(7,3)]
  | 56 => some [(4,1),(8,1)]
  | 57 => some [(0,2),(6,5)]
  | 58 => some [(0,4)]
  | 59 => some [(5,4)]
  | _ => some [(6,4)]
theorem root4Node13Domains1_fast_eq : root4Node13Domains1 = expandDomains root4Node13Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node13Domains1 v = expandDomains root4Node13Domains1Fast v from by decide) v
theorem root4Node13Step1Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root4Node13Domains0 root4Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node13Domains0 root4Node13Domains1
    root4Node13Domains0Fast root4Node13Domains1Fast
    root4Node13Domains0_fast_eq root4Node13Domains1_fast_eq (by decide)
theorem root4Node13Step1_checked :
    checkReplacement table40 root4Node13Domains0 root4Node13Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node13Step1Chunk0_0_checked, root4Node13Step1Chunk0_1_checked, root4Node13Step1Chunk0_2_checked, root4Node13Step1Chunk0_3_checked, root4Node13Step1Chunk0_4_checked, root4Node13Step1Chunk0_5_checked, root4Node13Step1Chunk1_0_checked, root4Node13Step1Chunk1_1_checked, root4Node13Step1Chunk1_2_checked, root4Node13Step1Chunk1_3_checked, root4Node13Step1Chunk1_4_checked, root4Node13Step1Chunk1_5_checked, root4Node13Step1Chunk2_0_checked, root4Node13Step1Chunk2_1_checked, root4Node13Step1Chunk2_2_checked, root4Node13Step1Chunk2_3_checked, root4Node13Step1Chunk2_4_checked, root4Node13Step1Chunk2_5_checked, root4Node13Step1Chunk3_0_checked, root4Node13Step1Chunk3_1_checked, root4Node13Step1Chunk3_2_checked, root4Node13Step1Chunk3_3_checked, root4Node13Step1Chunk3_4_checked, root4Node13Step1Chunk3_5_checked, root4Node13Step1Chunk4_0_checked, root4Node13Step1Chunk4_1_checked, root4Node13Step1Chunk4_2_checked, root4Node13Step1Chunk4_3_checked, root4Node13Step1Chunk4_4_checked, root4Node13Step1Chunk4_5_checked, root4Node13Step1Chunk5_0_checked, root4Node13Step1Chunk5_1_checked, root4Node13Step1Chunk5_2_checked, root4Node13Step1Chunk5_3_checked, root4Node13Step1Chunk5_4_checked, root4Node13Step1Chunk5_5_checked, root4Node13Step1Chunk6_0_checked, root4Node13Step1Chunk6_1_checked, root4Node13Step1Chunk6_2_checked, root4Node13Step1Chunk6_3_checked, root4Node13Step1Chunk6_4_checked, root4Node13Step1Chunk6_5_checked, root4Node13Step1Chunk7_0_checked, root4Node13Step1Chunk7_1_checked, root4Node13Step1Chunk7_2_checked, root4Node13Step1Chunk7_3_checked, root4Node13Step1Chunk7_4_checked, root4Node13Step1Chunk7_5_checked, root4Node13Step1Chunk8_0_checked, root4Node13Step1Chunk8_1_checked, root4Node13Step1Chunk8_2_checked, root4Node13Step1Chunk8_3_checked, root4Node13Step1Chunk8_4_checked, root4Node13Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
