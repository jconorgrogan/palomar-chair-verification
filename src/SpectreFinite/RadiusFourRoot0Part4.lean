module

public import SpectreFinite.RadiusFourRoot0Part3
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable11
public import SpectreFinite.RadiusFourTable37
public import SpectreFinite.RadiusFourTable39
public import SpectreFinite.RadiusFourTable5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node7Domains4 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(8,1)]
  | 5 => [(7,2)]
  | 6 => [(7,4)]
  | 7 => [(1,3)]
  | 8 => [(4,2)]
  | 9 => [(5,3)]
  | 10 => [(5,5)]
  | 11 => [(1,1),(6,1)]
  | 12 => [(8,1)]
  | 13 => [(6,5)]
  | 14 => [(0,4)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(4,4)]
  | 18 => [(7,0),(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(3,0)]
  | 22 => [(2,5)]
  | 23 => [(6,0)]
  | 24 => [(7,1)]
  | 25 => [(7,5)]
  | 26 => [(4,4),(5,4),(8,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0)]
  | 33 => [(7,3)]
  | 34 => [(8,2)]
  | 35 => [(7,5)]
  | 36 => [(6,0)]
  | 37 => [(7,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1)]
  | 41 => [(0,1)]
  | 42 => [(6,2)]
  | 43 => [(8,2)]
  | 44 => [(5,0)]
  | 45 => [(4,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(8,5)]
  | 49 => [(1,0)]
  | 50 => [(5,4),(8,4)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3),(6,3)]
  | 55 => [(7,2),(8,2)]
  | 56 => [(1,5)]
  | 57 => [(6,1)]
  | 58 => [(4,1),(8,1)]
  | 59 => [(0,2),(6,5)]
  | _ => [(0,4),(1,1)]
def root0Node7Domains4Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(8,1)]
  | 5 => some [(7,2)]
  | 6 => some [(7,4)]
  | 7 => some [(1,3)]
  | 8 => some [(4,2)]
  | 9 => some [(5,3)]
  | 10 => some [(5,5)]
  | 11 => some [(1,1),(6,1)]
  | 12 => some [(8,1)]
  | 13 => some [(6,5)]
  | 14 => some [(0,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(7,0),(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(3,0)]
  | 22 => some [(2,5)]
  | 23 => some [(6,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(4,4),(5,4),(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(8,2)]
  | 44 => some [(5,0)]
  | 45 => some [(4,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(5,4),(8,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(1,5)]
  | 57 => some [(6,1)]
  | 58 => some [(4,1),(8,1)]
  | 59 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root0Node7Domains4_fast_eq : root0Node7Domains4 = expandDomains root0Node7Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node7Domains4 v = expandDomains root0Node7Domains4Fast v from by decide) v
theorem root0Node7Step4Chunk0_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_0⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk0_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_1⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk0_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_2⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk0_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_3⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk0_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_4⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk0_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_5⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk1_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_0⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk1_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_1⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk1_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_2⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk1_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_3⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk1_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_4⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk1_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_5⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk2_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_0⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk2_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_1⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk2_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_2⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk2_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_3⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk2_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_4⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk2_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_5⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk3_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_0⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk3_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_1⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk3_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_2⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk3_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_3⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk3_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_4⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk3_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_5⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk4_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_0⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk4_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_1⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk4_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_2⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk4_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_3⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk4_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_4⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk4_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_5⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk5_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_0⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk5_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_1⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk5_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_2⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk5_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_3⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk5_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_4⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk5_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_5⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk6_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_0⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk6_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_1⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk6_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_2⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk6_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_3⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk6_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_4⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk6_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_5⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk7_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_0⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk7_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_1⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk7_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_2⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk7_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_3⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk7_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_4⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk7_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_5⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk8_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_0⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk8_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_1⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk8_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_2⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk8_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_3⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk8_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_4⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4Chunk8_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_5⟩
      root0Node7Domains3 root0Node7Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains3 root0Node7Domains4
    root0Node7Domains3Fast root0Node7Domains4Fast
    root0Node7Domains3_fast_eq root0Node7Domains4_fast_eq (by decide)
theorem root0Node7Step4_checked :
    checkReplacement table11 root0Node7Domains3 root0Node7Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node7Step4Chunk0_0_checked, root0Node7Step4Chunk0_1_checked, root0Node7Step4Chunk0_2_checked, root0Node7Step4Chunk0_3_checked, root0Node7Step4Chunk0_4_checked, root0Node7Step4Chunk0_5_checked, root0Node7Step4Chunk1_0_checked, root0Node7Step4Chunk1_1_checked, root0Node7Step4Chunk1_2_checked, root0Node7Step4Chunk1_3_checked, root0Node7Step4Chunk1_4_checked, root0Node7Step4Chunk1_5_checked, root0Node7Step4Chunk2_0_checked, root0Node7Step4Chunk2_1_checked, root0Node7Step4Chunk2_2_checked, root0Node7Step4Chunk2_3_checked, root0Node7Step4Chunk2_4_checked, root0Node7Step4Chunk2_5_checked, root0Node7Step4Chunk3_0_checked, root0Node7Step4Chunk3_1_checked, root0Node7Step4Chunk3_2_checked, root0Node7Step4Chunk3_3_checked, root0Node7Step4Chunk3_4_checked, root0Node7Step4Chunk3_5_checked, root0Node7Step4Chunk4_0_checked, root0Node7Step4Chunk4_1_checked, root0Node7Step4Chunk4_2_checked, root0Node7Step4Chunk4_3_checked, root0Node7Step4Chunk4_4_checked, root0Node7Step4Chunk4_5_checked, root0Node7Step4Chunk5_0_checked, root0Node7Step4Chunk5_1_checked, root0Node7Step4Chunk5_2_checked, root0Node7Step4Chunk5_3_checked, root0Node7Step4Chunk5_4_checked, root0Node7Step4Chunk5_5_checked, root0Node7Step4Chunk6_0_checked, root0Node7Step4Chunk6_1_checked, root0Node7Step4Chunk6_2_checked, root0Node7Step4Chunk6_3_checked, root0Node7Step4Chunk6_4_checked, root0Node7Step4Chunk6_5_checked, root0Node7Step4Chunk7_0_checked, root0Node7Step4Chunk7_1_checked, root0Node7Step4Chunk7_2_checked, root0Node7Step4Chunk7_3_checked, root0Node7Step4Chunk7_4_checked, root0Node7Step4Chunk7_5_checked, root0Node7Step4Chunk8_0_checked, root0Node7Step4Chunk8_1_checked, root0Node7Step4Chunk8_2_checked, root0Node7Step4Chunk8_3_checked, root0Node7Step4Chunk8_4_checked, root0Node7Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node8Domains0 : Domains 61 State := restrict root0Node7Domains4 11 (1,1)
def root0Node8Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(8,1)]
  | 5 => some [(7,2)]
  | 6 => some [(7,4)]
  | 7 => some [(1,3)]
  | 8 => some [(4,2)]
  | 9 => some [(5,3)]
  | 10 => some [(5,5)]
  | 11 => some [(1,1)]
  | 12 => some [(8,1)]
  | 13 => some [(6,5)]
  | 14 => some [(0,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(7,0),(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(3,0)]
  | 22 => some [(2,5)]
  | 23 => some [(6,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(4,4),(5,4),(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(8,2)]
  | 44 => some [(5,0)]
  | 45 => some [(4,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(5,4),(8,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(1,5)]
  | 57 => some [(6,1)]
  | 58 => some [(4,1),(8,1)]
  | 59 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root0Node8Domains0_fast_eq : root0Node8Domains0 = expandDomains root0Node8Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node8Domains0 v = expandDomains root0Node8Domains0Fast v from by decide) v
def root0Node8Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(8,1)]
  | 5 => [(7,2)]
  | 6 => [(7,4)]
  | 7 => [(1,3)]
  | 8 => [(4,2)]
  | 9 => [(5,3)]
  | 10 => [(5,5)]
  | 11 => [(1,1)]
  | 12 => [(8,1)]
  | 13 => [(6,5)]
  | 14 => [(0,4)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(4,4)]
  | 18 => [(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(3,0)]
  | 22 => [(2,5)]
  | 23 => [(6,0)]
  | 24 => [(7,1)]
  | 25 => [(7,5)]
  | 26 => [(5,4),(8,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0)]
  | 33 => [(7,3)]
  | 34 => [(8,2)]
  | 35 => [(7,5)]
  | 36 => [(6,0)]
  | 37 => [(7,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1)]
  | 41 => [(0,1)]
  | 42 => [(6,2)]
  | 43 => [(8,2)]
  | 44 => [(5,0)]
  | 45 => [(4,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(8,5)]
  | 49 => [(1,0)]
  | 50 => [(5,4),(8,4)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3),(6,3)]
  | 55 => [(7,2),(8,2)]
  | 56 => [(1,5)]
  | 57 => [(6,1)]
  | 58 => [(4,1),(8,1)]
  | 59 => [(0,2),(6,5)]
  | _ => [(0,4),(1,1)]
def root0Node8Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(8,1)]
  | 5 => some [(7,2)]
  | 6 => some [(7,4)]
  | 7 => some [(1,3)]
  | 8 => some [(4,2)]
  | 9 => some [(5,3)]
  | 10 => some [(5,5)]
  | 11 => some [(1,1)]
  | 12 => some [(8,1)]
  | 13 => some [(6,5)]
  | 14 => some [(0,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(3,0)]
  | 22 => some [(2,5)]
  | 23 => some [(6,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(5,4),(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(8,2)]
  | 44 => some [(5,0)]
  | 45 => some [(4,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(5,4),(8,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(1,5)]
  | 57 => some [(6,1)]
  | 58 => some [(4,1),(8,1)]
  | 59 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root0Node8Domains1_fast_eq : root0Node8Domains1 = expandDomains root0Node8Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node8Domains1 v = expandDomains root0Node8Domains1Fast v from by decide) v
theorem root0Node8Step1Chunk0_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_0⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk0_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_1⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk0_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_2⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk0_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_3⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk0_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_4⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk0_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_5⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk1_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_0⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk1_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_1⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk1_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_2⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk1_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_3⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk1_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_4⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk1_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_5⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk2_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_0⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk2_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_1⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk2_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_2⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk2_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_3⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk2_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_4⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk2_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_5⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk3_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_0⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk3_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_1⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk3_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_2⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk3_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_3⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk3_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_4⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk3_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_5⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk4_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_0⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk4_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_1⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk4_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_2⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk4_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_3⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk4_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_4⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk4_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_5⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk5_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_0⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk5_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_1⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk5_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_2⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk5_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_3⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk5_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_4⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk5_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_5⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk6_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_0⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk6_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_1⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk6_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_2⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk6_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_3⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk6_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_4⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk6_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_5⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk7_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_0⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk7_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_1⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk7_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_2⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk7_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_3⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk7_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_4⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk7_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_5⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk8_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_0⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk8_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_1⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk8_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_2⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk8_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_3⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk8_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_4⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1Chunk8_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_5⟩
      root0Node8Domains0 root0Node8Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node8Domains0 root0Node8Domains1
    root0Node8Domains0Fast root0Node8Domains1Fast
    root0Node8Domains0_fast_eq root0Node8Domains1_fast_eq (by decide)
theorem root0Node8Step1_checked :
    checkReplacement table5 root0Node8Domains0 root0Node8Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node8Step1Chunk0_0_checked, root0Node8Step1Chunk0_1_checked, root0Node8Step1Chunk0_2_checked, root0Node8Step1Chunk0_3_checked, root0Node8Step1Chunk0_4_checked, root0Node8Step1Chunk0_5_checked, root0Node8Step1Chunk1_0_checked, root0Node8Step1Chunk1_1_checked, root0Node8Step1Chunk1_2_checked, root0Node8Step1Chunk1_3_checked, root0Node8Step1Chunk1_4_checked, root0Node8Step1Chunk1_5_checked, root0Node8Step1Chunk2_0_checked, root0Node8Step1Chunk2_1_checked, root0Node8Step1Chunk2_2_checked, root0Node8Step1Chunk2_3_checked, root0Node8Step1Chunk2_4_checked, root0Node8Step1Chunk2_5_checked, root0Node8Step1Chunk3_0_checked, root0Node8Step1Chunk3_1_checked, root0Node8Step1Chunk3_2_checked, root0Node8Step1Chunk3_3_checked, root0Node8Step1Chunk3_4_checked, root0Node8Step1Chunk3_5_checked, root0Node8Step1Chunk4_0_checked, root0Node8Step1Chunk4_1_checked, root0Node8Step1Chunk4_2_checked, root0Node8Step1Chunk4_3_checked, root0Node8Step1Chunk4_4_checked, root0Node8Step1Chunk4_5_checked, root0Node8Step1Chunk5_0_checked, root0Node8Step1Chunk5_1_checked, root0Node8Step1Chunk5_2_checked, root0Node8Step1Chunk5_3_checked, root0Node8Step1Chunk5_4_checked, root0Node8Step1Chunk5_5_checked, root0Node8Step1Chunk6_0_checked, root0Node8Step1Chunk6_1_checked, root0Node8Step1Chunk6_2_checked, root0Node8Step1Chunk6_3_checked, root0Node8Step1Chunk6_4_checked, root0Node8Step1Chunk6_5_checked, root0Node8Step1Chunk7_0_checked, root0Node8Step1Chunk7_1_checked, root0Node8Step1Chunk7_2_checked, root0Node8Step1Chunk7_3_checked, root0Node8Step1Chunk7_4_checked, root0Node8Step1Chunk7_5_checked, root0Node8Step1Chunk8_0_checked, root0Node8Step1Chunk8_1_checked, root0Node8Step1Chunk8_2_checked, root0Node8Step1Chunk8_3_checked, root0Node8Step1Chunk8_4_checked, root0Node8Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node9Domains0 : Domains 61 State := restrict root0Node8Domains1 26 (5,4)
def root0Node9Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(8,1)]
  | 5 => some [(7,2)]
  | 6 => some [(7,4)]
  | 7 => some [(1,3)]
  | 8 => some [(4,2)]
  | 9 => some [(5,3)]
  | 10 => some [(5,5)]
  | 11 => some [(1,1)]
  | 12 => some [(8,1)]
  | 13 => some [(6,5)]
  | 14 => some [(0,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(3,0)]
  | 22 => some [(2,5)]
  | 23 => some [(6,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(5,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(8,2)]
  | 44 => some [(5,0)]
  | 45 => some [(4,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(5,4),(8,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(1,5)]
  | 57 => some [(6,1)]
  | 58 => some [(4,1),(8,1)]
  | 59 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root0Node9Domains0_fast_eq : root0Node9Domains0 = expandDomains root0Node9Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node9Domains0 v = expandDomains root0Node9Domains0Fast v from by decide) v
def root0Node9Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(8,1)]
  | 5 => [(7,2)]
  | 6 => [(7,4)]
  | 7 => [(1,3)]
  | 8 => [(4,2)]
  | 9 => [(5,3)]
  | 10 => [(5,5)]
  | 11 => [(1,1)]
  | 12 => [(8,1)]
  | 13 => [(6,5)]
  | 14 => [(0,4)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(4,4)]
  | 18 => [(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(3,0)]
  | 22 => [(2,5)]
  | 23 => [(6,0)]
  | 24 => [(7,1)]
  | 25 => [(7,5)]
  | 26 => [(5,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0)]
  | 33 => [(7,3)]
  | 34 => [(8,2)]
  | 35 => [(7,5)]
  | 36 => [(6,0)]
  | 37 => [(7,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1)]
  | 41 => [(0,1)]
  | 42 => [(6,2)]
  | 43 => [(8,2)]
  | 44 => [(5,0)]
  | 45 => [(4,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(8,5)]
  | 49 => [(1,0)]
  | 50 => [(5,4)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3),(6,3)]
  | 55 => [(7,2),(8,2)]
  | 56 => [(1,5)]
  | 57 => [(6,1)]
  | 58 => [(4,1)]
  | 59 => [(0,2),(6,5)]
  | _ => [(0,4),(1,1)]
def root0Node9Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(8,1)]
  | 5 => some [(7,2)]
  | 6 => some [(7,4)]
  | 7 => some [(1,3)]
  | 8 => some [(4,2)]
  | 9 => some [(5,3)]
  | 10 => some [(5,5)]
  | 11 => some [(1,1)]
  | 12 => some [(8,1)]
  | 13 => some [(6,5)]
  | 14 => some [(0,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(3,0)]
  | 22 => some [(2,5)]
  | 23 => some [(6,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(5,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(8,2)]
  | 44 => some [(5,0)]
  | 45 => some [(4,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(5,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(1,5)]
  | 57 => some [(6,1)]
  | 58 => some [(4,1)]
  | 59 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root0Node9Domains1_fast_eq : root0Node9Domains1 = expandDomains root0Node9Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node9Domains1 v = expandDomains root0Node9Domains1Fast v from by decide) v
theorem root0Node9Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root0Node9Domains0 root0Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains0 root0Node9Domains1
    root0Node9Domains0Fast root0Node9Domains1Fast
    root0Node9Domains0_fast_eq root0Node9Domains1_fast_eq (by decide)
theorem root0Node9Step1_checked :
    checkReplacement table37 root0Node9Domains0 root0Node9Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node9Step1Chunk0_0_checked, root0Node9Step1Chunk0_1_checked, root0Node9Step1Chunk0_2_checked, root0Node9Step1Chunk0_3_checked, root0Node9Step1Chunk0_4_checked, root0Node9Step1Chunk0_5_checked, root0Node9Step1Chunk1_0_checked, root0Node9Step1Chunk1_1_checked, root0Node9Step1Chunk1_2_checked, root0Node9Step1Chunk1_3_checked, root0Node9Step1Chunk1_4_checked, root0Node9Step1Chunk1_5_checked, root0Node9Step1Chunk2_0_checked, root0Node9Step1Chunk2_1_checked, root0Node9Step1Chunk2_2_checked, root0Node9Step1Chunk2_3_checked, root0Node9Step1Chunk2_4_checked, root0Node9Step1Chunk2_5_checked, root0Node9Step1Chunk3_0_checked, root0Node9Step1Chunk3_1_checked, root0Node9Step1Chunk3_2_checked, root0Node9Step1Chunk3_3_checked, root0Node9Step1Chunk3_4_checked, root0Node9Step1Chunk3_5_checked, root0Node9Step1Chunk4_0_checked, root0Node9Step1Chunk4_1_checked, root0Node9Step1Chunk4_2_checked, root0Node9Step1Chunk4_3_checked, root0Node9Step1Chunk4_4_checked, root0Node9Step1Chunk4_5_checked, root0Node9Step1Chunk5_0_checked, root0Node9Step1Chunk5_1_checked, root0Node9Step1Chunk5_2_checked, root0Node9Step1Chunk5_3_checked, root0Node9Step1Chunk5_4_checked, root0Node9Step1Chunk5_5_checked, root0Node9Step1Chunk6_0_checked, root0Node9Step1Chunk6_1_checked, root0Node9Step1Chunk6_2_checked, root0Node9Step1Chunk6_3_checked, root0Node9Step1Chunk6_4_checked, root0Node9Step1Chunk6_5_checked, root0Node9Step1Chunk7_0_checked, root0Node9Step1Chunk7_1_checked, root0Node9Step1Chunk7_2_checked, root0Node9Step1Chunk7_3_checked, root0Node9Step1Chunk7_4_checked, root0Node9Step1Chunk7_5_checked, root0Node9Step1Chunk8_0_checked, root0Node9Step1Chunk8_1_checked, root0Node9Step1Chunk8_2_checked, root0Node9Step1Chunk8_3_checked, root0Node9Step1Chunk8_4_checked, root0Node9Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node9Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(8,1)]
  | 5 => [(7,2)]
  | 6 => [(7,4)]
  | 7 => [(1,3)]
  | 8 => [(4,2)]
  | 9 => [(5,3)]
  | 10 => [(5,5)]
  | 11 => [(1,1)]
  | 12 => [(8,1)]
  | 13 => [(6,5)]
  | 14 => [(0,4)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(4,4)]
  | 18 => [(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(3,0)]
  | 22 => [(2,5)]
  | 23 => [(6,0)]
  | 24 => [(7,1)]
  | 25 => [(7,5)]
  | 26 => [(5,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0)]
  | 33 => [(7,3)]
  | 34 => [(8,2)]
  | 35 => [(7,5)]
  | 36 => [(6,0)]
  | 37 => [(7,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1)]
  | 41 => [(0,1)]
  | 42 => [(6,2)]
  | 43 => [(8,2)]
  | 44 => [(5,0)]
  | 45 => [(4,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(8,5)]
  | 49 => [(1,0)]
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
def root0Node9Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(8,1)]
  | 5 => some [(7,2)]
  | 6 => some [(7,4)]
  | 7 => some [(1,3)]
  | 8 => some [(4,2)]
  | 9 => some [(5,3)]
  | 10 => some [(5,5)]
  | 11 => some [(1,1)]
  | 12 => some [(8,1)]
  | 13 => some [(6,5)]
  | 14 => some [(0,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(3,0)]
  | 22 => some [(2,5)]
  | 23 => some [(6,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(5,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(8,2)]
  | 44 => some [(5,0)]
  | 45 => some [(4,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
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
theorem root0Node9Domains2_fast_eq : root0Node9Domains2 = expandDomains root0Node9Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node9Domains2 v = expandDomains root0Node9Domains2Fast v from by decide) v
theorem root0Node9Step2Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root0Node9Domains1 root0Node9Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node9Domains1 root0Node9Domains2
    root0Node9Domains1Fast root0Node9Domains2Fast
    root0Node9Domains1_fast_eq root0Node9Domains2_fast_eq (by decide)
theorem root0Node9Step2_checked :
    checkReplacement table39 root0Node9Domains1 root0Node9Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node9Step2Chunk0_0_checked, root0Node9Step2Chunk0_1_checked, root0Node9Step2Chunk0_2_checked, root0Node9Step2Chunk0_3_checked, root0Node9Step2Chunk0_4_checked, root0Node9Step2Chunk0_5_checked, root0Node9Step2Chunk1_0_checked, root0Node9Step2Chunk1_1_checked, root0Node9Step2Chunk1_2_checked, root0Node9Step2Chunk1_3_checked, root0Node9Step2Chunk1_4_checked, root0Node9Step2Chunk1_5_checked, root0Node9Step2Chunk2_0_checked, root0Node9Step2Chunk2_1_checked, root0Node9Step2Chunk2_2_checked, root0Node9Step2Chunk2_3_checked, root0Node9Step2Chunk2_4_checked, root0Node9Step2Chunk2_5_checked, root0Node9Step2Chunk3_0_checked, root0Node9Step2Chunk3_1_checked, root0Node9Step2Chunk3_2_checked, root0Node9Step2Chunk3_3_checked, root0Node9Step2Chunk3_4_checked, root0Node9Step2Chunk3_5_checked, root0Node9Step2Chunk4_0_checked, root0Node9Step2Chunk4_1_checked, root0Node9Step2Chunk4_2_checked, root0Node9Step2Chunk4_3_checked, root0Node9Step2Chunk4_4_checked, root0Node9Step2Chunk4_5_checked, root0Node9Step2Chunk5_0_checked, root0Node9Step2Chunk5_1_checked, root0Node9Step2Chunk5_2_checked, root0Node9Step2Chunk5_3_checked, root0Node9Step2Chunk5_4_checked, root0Node9Step2Chunk5_5_checked, root0Node9Step2Chunk6_0_checked, root0Node9Step2Chunk6_1_checked, root0Node9Step2Chunk6_2_checked, root0Node9Step2Chunk6_3_checked, root0Node9Step2Chunk6_4_checked, root0Node9Step2Chunk6_5_checked, root0Node9Step2Chunk7_0_checked, root0Node9Step2Chunk7_1_checked, root0Node9Step2Chunk7_2_checked, root0Node9Step2Chunk7_3_checked, root0Node9Step2Chunk7_4_checked, root0Node9Step2Chunk7_5_checked, root0Node9Step2Chunk8_0_checked, root0Node9Step2Chunk8_1_checked, root0Node9Step2Chunk8_2_checked, root0Node9Step2Chunk8_3_checked, root0Node9Step2Chunk8_4_checked, root0Node9Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root0Node9Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node9Domains2 (.output 3) = true := by decide
def root0Node10Domains0 : Domains 61 State := restrict root0Node8Domains1 26 (8,4)
def root0Node10Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(8,1)]
  | 5 => some [(7,2)]
  | 6 => some [(7,4)]
  | 7 => some [(1,3)]
  | 8 => some [(4,2)]
  | 9 => some [(5,3)]
  | 10 => some [(5,5)]
  | 11 => some [(1,1)]
  | 12 => some [(8,1)]
  | 13 => some [(6,5)]
  | 14 => some [(0,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(3,0)]
  | 22 => some [(2,5)]
  | 23 => some [(6,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(8,2)]
  | 44 => some [(5,0)]
  | 45 => some [(4,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(5,4),(8,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(1,5)]
  | 57 => some [(6,1)]
  | 58 => some [(4,1),(8,1)]
  | 59 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root0Node10Domains0_fast_eq : root0Node10Domains0 = expandDomains root0Node10Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node10Domains0 v = expandDomains root0Node10Domains0Fast v from by decide) v
def root0Node10Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(8,1)]
  | 5 => [(7,2)]
  | 6 => [(7,4)]
  | 7 => [(1,3)]
  | 8 => [(4,2)]
  | 9 => [(5,3)]
  | 10 => [(5,5)]
  | 11 => [(1,1)]
  | 12 => [(8,1)]
  | 13 => [(6,5)]
  | 14 => [(0,4)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(4,4)]
  | 18 => [(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(3,0)]
  | 22 => [(2,5)]
  | 23 => [(6,0)]
  | 24 => [(7,1)]
  | 25 => [(7,5)]
  | 26 => [(8,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0)]
  | 33 => [(7,3)]
  | 34 => [(8,2)]
  | 35 => [(7,5)]
  | 36 => [(6,0)]
  | 37 => [(7,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1)]
  | 41 => [(0,1)]
  | 42 => [(6,2)]
  | 43 => [(8,2)]
  | 44 => [(5,0)]
  | 45 => [(4,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(8,5)]
  | 49 => [(1,0)]
  | 50 => [(8,4)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3),(6,3)]
  | 55 => [(7,2),(8,2)]
  | 56 => [(1,5)]
  | 57 => [(6,1)]
  | 58 => [(8,1)]
  | 59 => [(0,2),(6,5)]
  | _ => [(0,4),(1,1)]
def root0Node10Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(8,1)]
  | 5 => some [(7,2)]
  | 6 => some [(7,4)]
  | 7 => some [(1,3)]
  | 8 => some [(4,2)]
  | 9 => some [(5,3)]
  | 10 => some [(5,5)]
  | 11 => some [(1,1)]
  | 12 => some [(8,1)]
  | 13 => some [(6,5)]
  | 14 => some [(0,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(4,4)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(3,0)]
  | 22 => some [(2,5)]
  | 23 => some [(6,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(8,2)]
  | 44 => some [(5,0)]
  | 45 => some [(4,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(8,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(1,5)]
  | 57 => some [(6,1)]
  | 58 => some [(8,1)]
  | 59 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root0Node10Domains1_fast_eq : root0Node10Domains1 = expandDomains root0Node10Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node10Domains1 v = expandDomains root0Node10Domains1Fast v from by decide) v
theorem root0Node10Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root0Node10Domains0 root0Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node10Domains0 root0Node10Domains1
    root0Node10Domains0Fast root0Node10Domains1Fast
    root0Node10Domains0_fast_eq root0Node10Domains1_fast_eq (by decide)
theorem root0Node10Step1_checked :
    checkReplacement table37 root0Node10Domains0 root0Node10Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node10Step1Chunk0_0_checked, root0Node10Step1Chunk0_1_checked, root0Node10Step1Chunk0_2_checked, root0Node10Step1Chunk0_3_checked, root0Node10Step1Chunk0_4_checked, root0Node10Step1Chunk0_5_checked, root0Node10Step1Chunk1_0_checked, root0Node10Step1Chunk1_1_checked, root0Node10Step1Chunk1_2_checked, root0Node10Step1Chunk1_3_checked, root0Node10Step1Chunk1_4_checked, root0Node10Step1Chunk1_5_checked, root0Node10Step1Chunk2_0_checked, root0Node10Step1Chunk2_1_checked, root0Node10Step1Chunk2_2_checked, root0Node10Step1Chunk2_3_checked, root0Node10Step1Chunk2_4_checked, root0Node10Step1Chunk2_5_checked, root0Node10Step1Chunk3_0_checked, root0Node10Step1Chunk3_1_checked, root0Node10Step1Chunk3_2_checked, root0Node10Step1Chunk3_3_checked, root0Node10Step1Chunk3_4_checked, root0Node10Step1Chunk3_5_checked, root0Node10Step1Chunk4_0_checked, root0Node10Step1Chunk4_1_checked, root0Node10Step1Chunk4_2_checked, root0Node10Step1Chunk4_3_checked, root0Node10Step1Chunk4_4_checked, root0Node10Step1Chunk4_5_checked, root0Node10Step1Chunk5_0_checked, root0Node10Step1Chunk5_1_checked, root0Node10Step1Chunk5_2_checked, root0Node10Step1Chunk5_3_checked, root0Node10Step1Chunk5_4_checked, root0Node10Step1Chunk5_5_checked, root0Node10Step1Chunk6_0_checked, root0Node10Step1Chunk6_1_checked, root0Node10Step1Chunk6_2_checked, root0Node10Step1Chunk6_3_checked, root0Node10Step1Chunk6_4_checked, root0Node10Step1Chunk6_5_checked, root0Node10Step1Chunk7_0_checked, root0Node10Step1Chunk7_1_checked, root0Node10Step1Chunk7_2_checked, root0Node10Step1Chunk7_3_checked, root0Node10Step1Chunk7_4_checked, root0Node10Step1Chunk7_5_checked, root0Node10Step1Chunk8_0_checked, root0Node10Step1Chunk8_1_checked, root0Node10Step1Chunk8_2_checked, root0Node10Step1Chunk8_3_checked, root0Node10Step1Chunk8_4_checked, root0Node10Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
