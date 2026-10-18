module

public import SpectreFinite.RadiusFourRoot7Part12
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable23
public import SpectreFinite.RadiusFourTable26
public import SpectreFinite.RadiusFourTable29
public import SpectreFinite.RadiusFourTable35
public import SpectreFinite.RadiusFourTable39

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node35Domains4 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(6,0)]
  | 2 => [(7,1)]
  | 3 => [(1,5)]
  | 4 => [(6,1)]
  | 5 => [(7,3)]
  | 6 => [(8,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(0,1),(6,4)]
  | 12 => [(1,2),(6,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(1,3)]
  | 18 => [(7,5),(8,5)]
  | 19 => [(0,3),(1,0)]
  | 20 => [(7,1),(8,1)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(8,1)]
  | 24 => [(6,5)]
  | 25 => [(0,4)]
  | 26 => [(1,3)]
  | 27 => [(4,2),(8,2)]
  | 28 => [(5,0),(5,3)]
  | 29 => [(4,5),(5,5),(8,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(5,5),(8,5)]
  | 33 => [(7,0)]
  | 34 => [(4,3)]
  | 35 => [(0,4)]
  | 36 => [(1,4),(3,4),(5,4)]
  | 37 => [(0,0),(0,5),(6,3)]
  | 38 => [(4,4),(7,2)]
  | 39 => [(1,4),(7,4)]
  | 40 => [(0,5),(6,3)]
  | 41 => [(4,4),(7,2)]
  | 42 => [(1,4),(7,4)]
  | 43 => [(2,3),(2,5),(4,3)]
  | 44 => [(0,2),(1,5),(6,0)]
  | 45 => [(1,1),(6,1),(7,1)]
  | 46 => [(4,1),(7,5)]
  | 47 => [(0,2),(6,0)]
  | 48 => [(1,1),(7,1)]
  | 49 => [(4,1),(7,5),(8,1)]
  | 50 => [(0,5),(1,2),(7,2)]
  | 51 => [(2,0),(4,0)]
  | 52 => [(7,3)]
  | 53 => [(5,2),(8,2)]
  | 54 => [(8,0)]
  | 55 => [(7,3),(8,3)]
  | 56 => [(3,1),(5,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(8,4)]
  | _ => [(1,4),(6,4)]
def root7Node35Domains4Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(6,0)]
  | 2 => some [(7,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(7,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(0,1),(6,4)]
  | 12 => some [(1,2),(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3)]
  | 18 => some [(7,5),(8,5)]
  | 19 => some [(0,3),(1,0)]
  | 20 => some [(7,1),(8,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(1,3)]
  | 27 => some [(4,2),(8,2)]
  | 28 => some [(5,0),(5,3)]
  | 29 => some [(4,5),(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5),(8,5)]
  | 33 => some [(7,0)]
  | 34 => some [(4,3)]
  | 35 => some [(0,4)]
  | 36 => some [(1,4),(3,4),(5,4)]
  | 37 => some [(0,0),(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(7,4)]
  | 40 => some [(0,5),(6,3)]
  | 41 => some [(4,4),(7,2)]
  | 42 => some [(1,4),(7,4)]
  | 43 => some [(2,3),(2,5),(4,3)]
  | 44 => some [(0,2),(1,5),(6,0)]
  | 45 => some [(1,1),(6,1),(7,1)]
  | 46 => some [(4,1),(7,5)]
  | 47 => some [(0,2),(6,0)]
  | 48 => some [(1,1),(7,1)]
  | 49 => some [(4,1),(7,5),(8,1)]
  | 50 => some [(0,5),(1,2),(7,2)]
  | 51 => some [(2,0),(4,0)]
  | 52 => some [(7,3)]
  | 53 => some [(5,2),(8,2)]
  | 54 => some [(8,0)]
  | 55 => some [(7,3),(8,3)]
  | 56 => some [(3,1),(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(1,4),(6,4)]
theorem root7Node35Domains4_fast_eq : root7Node35Domains4 = expandDomains root7Node35Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node35Domains4 v = expandDomains root7Node35Domains4Fast v from by decide) v
theorem root7Node35Step4Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root7Node35Domains3 root7Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node35Domains3 root7Node35Domains4
    root7Node35Domains3Fast root7Node35Domains4Fast
    root7Node35Domains3_fast_eq root7Node35Domains4_fast_eq (by decide)
theorem root7Node35Step4_checked :
    checkReplacement table26 root7Node35Domains3 root7Node35Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node35Step4Chunk0_0_checked, root7Node35Step4Chunk0_1_checked, root7Node35Step4Chunk0_2_checked, root7Node35Step4Chunk0_3_checked, root7Node35Step4Chunk0_4_checked, root7Node35Step4Chunk0_5_checked, root7Node35Step4Chunk1_0_checked, root7Node35Step4Chunk1_1_checked, root7Node35Step4Chunk1_2_checked, root7Node35Step4Chunk1_3_checked, root7Node35Step4Chunk1_4_checked, root7Node35Step4Chunk1_5_checked, root7Node35Step4Chunk2_0_checked, root7Node35Step4Chunk2_1_checked, root7Node35Step4Chunk2_2_checked, root7Node35Step4Chunk2_3_checked, root7Node35Step4Chunk2_4_checked, root7Node35Step4Chunk2_5_checked, root7Node35Step4Chunk3_0_checked, root7Node35Step4Chunk3_1_checked, root7Node35Step4Chunk3_2_checked, root7Node35Step4Chunk3_3_checked, root7Node35Step4Chunk3_4_checked, root7Node35Step4Chunk3_5_checked, root7Node35Step4Chunk4_0_checked, root7Node35Step4Chunk4_1_checked, root7Node35Step4Chunk4_2_checked, root7Node35Step4Chunk4_3_checked, root7Node35Step4Chunk4_4_checked, root7Node35Step4Chunk4_5_checked, root7Node35Step4Chunk5_0_checked, root7Node35Step4Chunk5_1_checked, root7Node35Step4Chunk5_2_checked, root7Node35Step4Chunk5_3_checked, root7Node35Step4Chunk5_4_checked, root7Node35Step4Chunk5_5_checked, root7Node35Step4Chunk6_0_checked, root7Node35Step4Chunk6_1_checked, root7Node35Step4Chunk6_2_checked, root7Node35Step4Chunk6_3_checked, root7Node35Step4Chunk6_4_checked, root7Node35Step4Chunk6_5_checked, root7Node35Step4Chunk7_0_checked, root7Node35Step4Chunk7_1_checked, root7Node35Step4Chunk7_2_checked, root7Node35Step4Chunk7_3_checked, root7Node35Step4Chunk7_4_checked, root7Node35Step4Chunk7_5_checked, root7Node35Step4Chunk8_0_checked, root7Node35Step4Chunk8_1_checked, root7Node35Step4Chunk8_2_checked, root7Node35Step4Chunk8_3_checked, root7Node35Step4Chunk8_4_checked, root7Node35Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node36Domains0 : Domains 61 State := restrict root7Node35Domains4 11 (0,1)
def root7Node36Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(6,0)]
  | 2 => some [(7,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(7,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(0,1)]
  | 12 => some [(1,2),(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3)]
  | 18 => some [(7,5),(8,5)]
  | 19 => some [(0,3),(1,0)]
  | 20 => some [(7,1),(8,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(1,3)]
  | 27 => some [(4,2),(8,2)]
  | 28 => some [(5,0),(5,3)]
  | 29 => some [(4,5),(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5),(8,5)]
  | 33 => some [(7,0)]
  | 34 => some [(4,3)]
  | 35 => some [(0,4)]
  | 36 => some [(1,4),(3,4),(5,4)]
  | 37 => some [(0,0),(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(7,4)]
  | 40 => some [(0,5),(6,3)]
  | 41 => some [(4,4),(7,2)]
  | 42 => some [(1,4),(7,4)]
  | 43 => some [(2,3),(2,5),(4,3)]
  | 44 => some [(0,2),(1,5),(6,0)]
  | 45 => some [(1,1),(6,1),(7,1)]
  | 46 => some [(4,1),(7,5)]
  | 47 => some [(0,2),(6,0)]
  | 48 => some [(1,1),(7,1)]
  | 49 => some [(4,1),(7,5),(8,1)]
  | 50 => some [(0,5),(1,2),(7,2)]
  | 51 => some [(2,0),(4,0)]
  | 52 => some [(7,3)]
  | 53 => some [(5,2),(8,2)]
  | 54 => some [(8,0)]
  | 55 => some [(7,3),(8,3)]
  | 56 => some [(3,1),(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(1,4),(6,4)]
theorem root7Node36Domains0_fast_eq : root7Node36Domains0 = expandDomains root7Node36Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node36Domains0 v = expandDomains root7Node36Domains0Fast v from by decide) v
def root7Node36Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(6,0)]
  | 2 => [(7,1)]
  | 3 => [(1,5)]
  | 4 => [(6,1)]
  | 5 => [(7,3)]
  | 6 => [(8,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(1,3)]
  | 18 => [(8,5)]
  | 19 => [(1,0)]
  | 20 => [(7,1)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(8,1)]
  | 24 => [(6,5)]
  | 25 => [(0,4)]
  | 26 => [(1,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(8,5)]
  | 33 => [(7,0)]
  | 34 => [(4,3)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(6,3)]
  | 41 => [(4,4),(7,2)]
  | 42 => [(1,4),(7,4)]
  | 43 => [(4,3)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(4,1)]
  | 47 => [(0,2)]
  | 48 => [(1,1),(7,1)]
  | 49 => [(4,1),(7,5),(8,1)]
  | 50 => [(0,5)]
  | 51 => [(2,0)]
  | 52 => [(7,3)]
  | 53 => [(5,2)]
  | 54 => [(8,0)]
  | 55 => [(7,3),(8,3)]
  | 56 => [(3,1),(5,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(8,4)]
  | _ => [(1,4),(6,4)]
def root7Node36Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(6,0)]
  | 2 => some [(7,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(7,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3)]
  | 18 => some [(8,5)]
  | 19 => some [(1,0)]
  | 20 => some [(7,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(1,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(7,0)]
  | 34 => some [(4,3)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(6,3)]
  | 41 => some [(4,4),(7,2)]
  | 42 => some [(1,4),(7,4)]
  | 43 => some [(4,3)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(4,1)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1),(7,1)]
  | 49 => some [(4,1),(7,5),(8,1)]
  | 50 => some [(0,5)]
  | 51 => some [(2,0)]
  | 52 => some [(7,3)]
  | 53 => some [(5,2)]
  | 54 => some [(8,0)]
  | 55 => some [(7,3),(8,3)]
  | 56 => some [(3,1),(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(1,4),(6,4)]
theorem root7Node36Domains1_fast_eq : root7Node36Domains1 = expandDomains root7Node36Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node36Domains1 v = expandDomains root7Node36Domains1Fast v from by decide) v
theorem root7Node36Step1Chunk0_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk0_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk0_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk0_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk0_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk0_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk1_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk1_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk1_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk1_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk1_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk1_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk2_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk2_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk2_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk2_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk2_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk2_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk3_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk3_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk3_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk3_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk3_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk3_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk4_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk4_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk4_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk4_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk4_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk4_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk5_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk5_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk5_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk5_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk5_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk5_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk6_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk6_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk6_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk6_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk6_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk6_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk7_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk7_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk7_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk7_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk7_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk7_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk8_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_0⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk8_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_1⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk8_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_2⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk8_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_3⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk8_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_4⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1Chunk8_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_5⟩
      root7Node36Domains0 root7Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains0 root7Node36Domains1
    root7Node36Domains0Fast root7Node36Domains1Fast
    root7Node36Domains0_fast_eq root7Node36Domains1_fast_eq (by decide)
theorem root7Node36Step1_checked :
    checkReplacement table29 root7Node36Domains0 root7Node36Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node36Step1Chunk0_0_checked, root7Node36Step1Chunk0_1_checked, root7Node36Step1Chunk0_2_checked, root7Node36Step1Chunk0_3_checked, root7Node36Step1Chunk0_4_checked, root7Node36Step1Chunk0_5_checked, root7Node36Step1Chunk1_0_checked, root7Node36Step1Chunk1_1_checked, root7Node36Step1Chunk1_2_checked, root7Node36Step1Chunk1_3_checked, root7Node36Step1Chunk1_4_checked, root7Node36Step1Chunk1_5_checked, root7Node36Step1Chunk2_0_checked, root7Node36Step1Chunk2_1_checked, root7Node36Step1Chunk2_2_checked, root7Node36Step1Chunk2_3_checked, root7Node36Step1Chunk2_4_checked, root7Node36Step1Chunk2_5_checked, root7Node36Step1Chunk3_0_checked, root7Node36Step1Chunk3_1_checked, root7Node36Step1Chunk3_2_checked, root7Node36Step1Chunk3_3_checked, root7Node36Step1Chunk3_4_checked, root7Node36Step1Chunk3_5_checked, root7Node36Step1Chunk4_0_checked, root7Node36Step1Chunk4_1_checked, root7Node36Step1Chunk4_2_checked, root7Node36Step1Chunk4_3_checked, root7Node36Step1Chunk4_4_checked, root7Node36Step1Chunk4_5_checked, root7Node36Step1Chunk5_0_checked, root7Node36Step1Chunk5_1_checked, root7Node36Step1Chunk5_2_checked, root7Node36Step1Chunk5_3_checked, root7Node36Step1Chunk5_4_checked, root7Node36Step1Chunk5_5_checked, root7Node36Step1Chunk6_0_checked, root7Node36Step1Chunk6_1_checked, root7Node36Step1Chunk6_2_checked, root7Node36Step1Chunk6_3_checked, root7Node36Step1Chunk6_4_checked, root7Node36Step1Chunk6_5_checked, root7Node36Step1Chunk7_0_checked, root7Node36Step1Chunk7_1_checked, root7Node36Step1Chunk7_2_checked, root7Node36Step1Chunk7_3_checked, root7Node36Step1Chunk7_4_checked, root7Node36Step1Chunk7_5_checked, root7Node36Step1Chunk8_0_checked, root7Node36Step1Chunk8_1_checked, root7Node36Step1Chunk8_2_checked, root7Node36Step1Chunk8_3_checked, root7Node36Step1Chunk8_4_checked, root7Node36Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node36Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(6,0)]
  | 2 => [(7,1)]
  | 3 => [(1,5)]
  | 4 => [(6,1)]
  | 5 => [(7,3)]
  | 6 => [(8,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(1,3)]
  | 18 => [(8,5)]
  | 19 => [(1,0)]
  | 20 => [(7,1)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(8,1)]
  | 24 => [(6,5)]
  | 25 => [(0,4)]
  | 26 => [(1,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(8,5)]
  | 33 => [(7,0)]
  | 34 => [(4,3)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(6,3)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(4,3)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(4,1)]
  | 47 => [(0,2)]
  | 48 => [(1,1)]
  | 49 => [(4,1),(8,1)]
  | 50 => [(0,5)]
  | 51 => [(2,0)]
  | 52 => [(7,3)]
  | 53 => [(5,2)]
  | 54 => [(8,0)]
  | 55 => [(7,3),(8,3)]
  | 56 => [(3,1),(5,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(8,4)]
  | _ => [(1,4),(6,4)]
def root7Node36Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(6,0)]
  | 2 => some [(7,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(7,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3)]
  | 18 => some [(8,5)]
  | 19 => some [(1,0)]
  | 20 => some [(7,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(1,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(7,0)]
  | 34 => some [(4,3)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(4,3)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(4,1)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,5)]
  | 51 => some [(2,0)]
  | 52 => some [(7,3)]
  | 53 => some [(5,2)]
  | 54 => some [(8,0)]
  | 55 => some [(7,3),(8,3)]
  | 56 => some [(3,1),(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(1,4),(6,4)]
theorem root7Node36Domains2_fast_eq : root7Node36Domains2 = expandDomains root7Node36Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node36Domains2 v = expandDomains root7Node36Domains2Fast v from by decide) v
theorem root7Node36Step2Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root7Node36Domains1 root7Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains1 root7Node36Domains2
    root7Node36Domains1Fast root7Node36Domains2Fast
    root7Node36Domains1_fast_eq root7Node36Domains2_fast_eq (by decide)
theorem root7Node36Step2_checked :
    checkReplacement table23 root7Node36Domains1 root7Node36Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node36Step2Chunk0_0_checked, root7Node36Step2Chunk0_1_checked, root7Node36Step2Chunk0_2_checked, root7Node36Step2Chunk0_3_checked, root7Node36Step2Chunk0_4_checked, root7Node36Step2Chunk0_5_checked, root7Node36Step2Chunk1_0_checked, root7Node36Step2Chunk1_1_checked, root7Node36Step2Chunk1_2_checked, root7Node36Step2Chunk1_3_checked, root7Node36Step2Chunk1_4_checked, root7Node36Step2Chunk1_5_checked, root7Node36Step2Chunk2_0_checked, root7Node36Step2Chunk2_1_checked, root7Node36Step2Chunk2_2_checked, root7Node36Step2Chunk2_3_checked, root7Node36Step2Chunk2_4_checked, root7Node36Step2Chunk2_5_checked, root7Node36Step2Chunk3_0_checked, root7Node36Step2Chunk3_1_checked, root7Node36Step2Chunk3_2_checked, root7Node36Step2Chunk3_3_checked, root7Node36Step2Chunk3_4_checked, root7Node36Step2Chunk3_5_checked, root7Node36Step2Chunk4_0_checked, root7Node36Step2Chunk4_1_checked, root7Node36Step2Chunk4_2_checked, root7Node36Step2Chunk4_3_checked, root7Node36Step2Chunk4_4_checked, root7Node36Step2Chunk4_5_checked, root7Node36Step2Chunk5_0_checked, root7Node36Step2Chunk5_1_checked, root7Node36Step2Chunk5_2_checked, root7Node36Step2Chunk5_3_checked, root7Node36Step2Chunk5_4_checked, root7Node36Step2Chunk5_5_checked, root7Node36Step2Chunk6_0_checked, root7Node36Step2Chunk6_1_checked, root7Node36Step2Chunk6_2_checked, root7Node36Step2Chunk6_3_checked, root7Node36Step2Chunk6_4_checked, root7Node36Step2Chunk6_5_checked, root7Node36Step2Chunk7_0_checked, root7Node36Step2Chunk7_1_checked, root7Node36Step2Chunk7_2_checked, root7Node36Step2Chunk7_3_checked, root7Node36Step2Chunk7_4_checked, root7Node36Step2Chunk7_5_checked, root7Node36Step2Chunk8_0_checked, root7Node36Step2Chunk8_1_checked, root7Node36Step2Chunk8_2_checked, root7Node36Step2Chunk8_3_checked, root7Node36Step2Chunk8_4_checked, root7Node36Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node36Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(6,0)]
  | 2 => [(7,1)]
  | 3 => [(1,5)]
  | 4 => [(6,1)]
  | 5 => [(7,3)]
  | 6 => [(8,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(1,3)]
  | 18 => [(8,5)]
  | 19 => [(1,0)]
  | 20 => [(7,1)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(8,1)]
  | 24 => [(6,5)]
  | 25 => [(0,4)]
  | 26 => [(1,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(8,5)]
  | 33 => [(7,0)]
  | 34 => [(4,3)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(6,3)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(4,3)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(4,1)]
  | 47 => [(0,2)]
  | 48 => [(1,1)]
  | 49 => [(4,1),(8,1)]
  | 50 => [(0,5)]
  | 51 => [(2,0)]
  | 52 => [(7,3)]
  | 53 => [(5,2)]
  | 54 => [(8,0)]
  | 55 => [(7,3),(8,3)]
  | 56 => [(3,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(8,4)]
  | _ => [(1,4),(6,4)]
def root7Node36Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(6,0)]
  | 2 => some [(7,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(7,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3)]
  | 18 => some [(8,5)]
  | 19 => some [(1,0)]
  | 20 => some [(7,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(1,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(7,0)]
  | 34 => some [(4,3)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(4,3)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(4,1)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,5)]
  | 51 => some [(2,0)]
  | 52 => some [(7,3)]
  | 53 => some [(5,2)]
  | 54 => some [(8,0)]
  | 55 => some [(7,3),(8,3)]
  | 56 => some [(3,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(1,4),(6,4)]
theorem root7Node36Domains3_fast_eq : root7Node36Domains3 = expandDomains root7Node36Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node36Domains3 v = expandDomains root7Node36Domains3Fast v from by decide) v
theorem root7Node36Step3Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root7Node36Domains2 root7Node36Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node36Domains2 root7Node36Domains3
    root7Node36Domains2Fast root7Node36Domains3Fast
    root7Node36Domains2_fast_eq root7Node36Domains3_fast_eq (by decide)
theorem root7Node36Step3_checked :
    checkReplacement table35 root7Node36Domains2 root7Node36Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node36Step3Chunk0_0_checked, root7Node36Step3Chunk0_1_checked, root7Node36Step3Chunk0_2_checked, root7Node36Step3Chunk0_3_checked, root7Node36Step3Chunk0_4_checked, root7Node36Step3Chunk0_5_checked, root7Node36Step3Chunk1_0_checked, root7Node36Step3Chunk1_1_checked, root7Node36Step3Chunk1_2_checked, root7Node36Step3Chunk1_3_checked, root7Node36Step3Chunk1_4_checked, root7Node36Step3Chunk1_5_checked, root7Node36Step3Chunk2_0_checked, root7Node36Step3Chunk2_1_checked, root7Node36Step3Chunk2_2_checked, root7Node36Step3Chunk2_3_checked, root7Node36Step3Chunk2_4_checked, root7Node36Step3Chunk2_5_checked, root7Node36Step3Chunk3_0_checked, root7Node36Step3Chunk3_1_checked, root7Node36Step3Chunk3_2_checked, root7Node36Step3Chunk3_3_checked, root7Node36Step3Chunk3_4_checked, root7Node36Step3Chunk3_5_checked, root7Node36Step3Chunk4_0_checked, root7Node36Step3Chunk4_1_checked, root7Node36Step3Chunk4_2_checked, root7Node36Step3Chunk4_3_checked, root7Node36Step3Chunk4_4_checked, root7Node36Step3Chunk4_5_checked, root7Node36Step3Chunk5_0_checked, root7Node36Step3Chunk5_1_checked, root7Node36Step3Chunk5_2_checked, root7Node36Step3Chunk5_3_checked, root7Node36Step3Chunk5_4_checked, root7Node36Step3Chunk5_5_checked, root7Node36Step3Chunk6_0_checked, root7Node36Step3Chunk6_1_checked, root7Node36Step3Chunk6_2_checked, root7Node36Step3Chunk6_3_checked, root7Node36Step3Chunk6_4_checked, root7Node36Step3Chunk6_5_checked, root7Node36Step3Chunk7_0_checked, root7Node36Step3Chunk7_1_checked, root7Node36Step3Chunk7_2_checked, root7Node36Step3Chunk7_3_checked, root7Node36Step3Chunk7_4_checked, root7Node36Step3Chunk7_5_checked, root7Node36Step3Chunk8_0_checked, root7Node36Step3Chunk8_1_checked, root7Node36Step3Chunk8_2_checked, root7Node36Step3Chunk8_3_checked, root7Node36Step3Chunk8_4_checked, root7Node36Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node37Domains0 : Domains 61 State := restrict root7Node36Domains3 49 (4,1)
def root7Node37Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(6,0)]
  | 2 => some [(7,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(7,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3)]
  | 18 => some [(8,5)]
  | 19 => some [(1,0)]
  | 20 => some [(7,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(1,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(7,0)]
  | 34 => some [(4,3)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(4,3)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(4,1)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,5)]
  | 51 => some [(2,0)]
  | 52 => some [(7,3)]
  | 53 => some [(5,2)]
  | 54 => some [(8,0)]
  | 55 => some [(7,3),(8,3)]
  | 56 => some [(3,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(1,4),(6,4)]
theorem root7Node37Domains0_fast_eq : root7Node37Domains0 = expandDomains root7Node37Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node37Domains0 v = expandDomains root7Node37Domains0Fast v from by decide) v
def root7Node37Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(6,0)]
  | 2 => [(7,1)]
  | 3 => [(1,5)]
  | 4 => [(6,1)]
  | 5 => [(7,3)]
  | 6 => [(8,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(1,3)]
  | 18 => [(8,5)]
  | 19 => [(1,0)]
  | 20 => [(7,1)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(8,1)]
  | 24 => [(6,5)]
  | 25 => [(0,4)]
  | 26 => [(1,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(8,5)]
  | 33 => [(7,0)]
  | 34 => [(4,3)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(6,3)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(4,3)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(4,1)]
  | 47 => [(0,2)]
  | 48 => [(1,1)]
  | 49 => [(4,1)]
  | 50 => [(0,5)]
  | 51 => [(2,0)]
  | 52 => [(7,3)]
  | 53 => [(5,2)]
  | 54 => [(8,0)]
  | 55 => [(7,3)]
  | 56 => [(3,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(8,4)]
  | _ => [(6,4)]
def root7Node37Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(6,0)]
  | 2 => some [(7,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(7,3)]
  | 6 => some [(8,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3)]
  | 18 => some [(8,5)]
  | 19 => some [(1,0)]
  | 20 => some [(7,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(1,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(7,0)]
  | 34 => some [(4,3)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(4,3)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(4,1)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,5)]
  | 51 => some [(2,0)]
  | 52 => some [(7,3)]
  | 53 => some [(5,2)]
  | 54 => some [(8,0)]
  | 55 => some [(7,3)]
  | 56 => some [(3,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(6,4)]
theorem root7Node37Domains1_fast_eq : root7Node37Domains1 = expandDomains root7Node37Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node37Domains1 v = expandDomains root7Node37Domains1Fast v from by decide) v
theorem root7Node37Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root7Node37Domains0 root7Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node37Domains0 root7Node37Domains1
    root7Node37Domains0Fast root7Node37Domains1Fast
    root7Node37Domains0_fast_eq root7Node37Domains1_fast_eq (by decide)
theorem root7Node37Step1_checked :
    checkReplacement table39 root7Node37Domains0 root7Node37Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node37Step1Chunk0_0_checked, root7Node37Step1Chunk0_1_checked, root7Node37Step1Chunk0_2_checked, root7Node37Step1Chunk0_3_checked, root7Node37Step1Chunk0_4_checked, root7Node37Step1Chunk0_5_checked, root7Node37Step1Chunk1_0_checked, root7Node37Step1Chunk1_1_checked, root7Node37Step1Chunk1_2_checked, root7Node37Step1Chunk1_3_checked, root7Node37Step1Chunk1_4_checked, root7Node37Step1Chunk1_5_checked, root7Node37Step1Chunk2_0_checked, root7Node37Step1Chunk2_1_checked, root7Node37Step1Chunk2_2_checked, root7Node37Step1Chunk2_3_checked, root7Node37Step1Chunk2_4_checked, root7Node37Step1Chunk2_5_checked, root7Node37Step1Chunk3_0_checked, root7Node37Step1Chunk3_1_checked, root7Node37Step1Chunk3_2_checked, root7Node37Step1Chunk3_3_checked, root7Node37Step1Chunk3_4_checked, root7Node37Step1Chunk3_5_checked, root7Node37Step1Chunk4_0_checked, root7Node37Step1Chunk4_1_checked, root7Node37Step1Chunk4_2_checked, root7Node37Step1Chunk4_3_checked, root7Node37Step1Chunk4_4_checked, root7Node37Step1Chunk4_5_checked, root7Node37Step1Chunk5_0_checked, root7Node37Step1Chunk5_1_checked, root7Node37Step1Chunk5_2_checked, root7Node37Step1Chunk5_3_checked, root7Node37Step1Chunk5_4_checked, root7Node37Step1Chunk5_5_checked, root7Node37Step1Chunk6_0_checked, root7Node37Step1Chunk6_1_checked, root7Node37Step1Chunk6_2_checked, root7Node37Step1Chunk6_3_checked, root7Node37Step1Chunk6_4_checked, root7Node37Step1Chunk6_5_checked, root7Node37Step1Chunk7_0_checked, root7Node37Step1Chunk7_1_checked, root7Node37Step1Chunk7_2_checked, root7Node37Step1Chunk7_3_checked, root7Node37Step1Chunk7_4_checked, root7Node37Step1Chunk7_5_checked, root7Node37Step1Chunk8_0_checked, root7Node37Step1Chunk8_1_checked, root7Node37Step1Chunk8_2_checked, root7Node37Step1Chunk8_3_checked, root7Node37Step1Chunk8_4_checked, root7Node37Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root7Node37Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node37Domains1 (.output 16) = true := by decide
end SpectreFinite.HexSearch.RadiusFour
