module

public import SpectreFinite.RadiusFourRoot1Part7
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable11
public import SpectreFinite.RadiusFourTable26
public import SpectreFinite.RadiusFourTable36
public import SpectreFinite.RadiusFourTable40

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node21Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(3,4),(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(2,1),(2,3)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(0,0),(6,4)]
  | 12 => [(1,2),(3,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(5,0),(8,0)]
  | 17 => [(4,5),(7,3),(8,3)]
  | 18 => [(1,5),(7,5)]
  | 19 => [(0,3),(6,1)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(0,0),(1,4),(6,4)]
  | 25 => [(0,5),(1,2),(7,2)]
  | 26 => [(4,5),(7,3)]
  | 27 => [(4,2),(7,0)]
  | 28 => [(5,3),(8,3)]
  | 29 => [(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5),(7,5)]
  | 33 => [(0,3),(6,0),(6,1)]
  | 34 => [(5,1),(7,1),(8,1)]
  | 35 => [(1,2),(7,2)]
  | 36 => [(7,4)]
  | 37 => [(1,3),(6,3)]
  | 38 => [(7,2),(8,2)]
  | 39 => [(4,0),(5,0),(8,0)]
  | 40 => [(4,5),(7,3)]
  | 41 => [(4,2),(7,0),(8,2)]
  | 42 => [(5,0),(5,3),(8,3)]
  | 43 => [(4,1),(8,1)]
  | 44 => [(0,2),(6,5)]
  | 45 => [(0,4),(1,1)]
  | 46 => [(5,1),(5,4)]
  | 47 => [(0,0),(0,1),(6,4)]
  | 48 => [(1,2),(6,2),(7,2)]
  | 49 => [(7,4),(8,4)]
  | 50 => [(5,2),(5,5),(8,5)]
  | 51 => [(7,0),(8,0)]
  | 52 => [(4,3),(8,3)]
  | 53 => [(1,5),(3,5),(5,5),(7,5)]
  | 54 => [(0,3),(1,0),(6,1)]
  | 55 => [(2,1),(4,1),(8,1)]
  | 56 => [(4,4),(5,4),(7,2),(8,4)]
  | 57 => [(1,4),(7,4)]
  | 58 => [(0,5),(1,3),(6,3)]
  | 59 => [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | _ => [(0,0),(1,3),(3,3),(5,3),(7,3)]
def root1Node21Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4),(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,1),(2,3)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(0,0),(6,4)]
  | 12 => some [(1,2),(3,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3),(8,3)]
  | 18 => some [(1,5),(7,5)]
  | 19 => some [(0,3),(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0),(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(7,2)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(4,2),(7,0)]
  | 28 => some [(5,3),(8,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(5,1),(7,1),(8,1)]
  | 35 => some [(1,2),(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3),(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(5,0),(5,3),(8,3)]
  | 43 => some [(4,1),(8,1)]
  | 44 => some [(0,2),(6,5)]
  | 45 => some [(0,4),(1,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,0),(0,1),(6,4)]
  | 48 => some [(1,2),(6,2),(7,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(1,5),(3,5),(5,5),(7,5)]
  | 54 => some [(0,3),(1,0),(6,1)]
  | 55 => some [(2,1),(4,1),(8,1)]
  | 56 => some [(4,4),(5,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(1,3),(6,3)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | _ => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
theorem root1Node21Domains3_fast_eq : root1Node21Domains3 = expandDomains root1Node21Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node21Domains3 v = expandDomains root1Node21Domains3Fast v from by decide) v
theorem root1Node21Step3Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root1Node21Domains2 root1Node21Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains2 root1Node21Domains3
    root1Node21Domains2Fast root1Node21Domains3Fast
    root1Node21Domains2_fast_eq root1Node21Domains3_fast_eq (by decide)
theorem root1Node21Step3_checked :
    checkReplacement table26 root1Node21Domains2 root1Node21Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node21Step3Chunk0_0_checked, root1Node21Step3Chunk0_1_checked, root1Node21Step3Chunk0_2_checked, root1Node21Step3Chunk0_3_checked, root1Node21Step3Chunk0_4_checked, root1Node21Step3Chunk0_5_checked, root1Node21Step3Chunk1_0_checked, root1Node21Step3Chunk1_1_checked, root1Node21Step3Chunk1_2_checked, root1Node21Step3Chunk1_3_checked, root1Node21Step3Chunk1_4_checked, root1Node21Step3Chunk1_5_checked, root1Node21Step3Chunk2_0_checked, root1Node21Step3Chunk2_1_checked, root1Node21Step3Chunk2_2_checked, root1Node21Step3Chunk2_3_checked, root1Node21Step3Chunk2_4_checked, root1Node21Step3Chunk2_5_checked, root1Node21Step3Chunk3_0_checked, root1Node21Step3Chunk3_1_checked, root1Node21Step3Chunk3_2_checked, root1Node21Step3Chunk3_3_checked, root1Node21Step3Chunk3_4_checked, root1Node21Step3Chunk3_5_checked, root1Node21Step3Chunk4_0_checked, root1Node21Step3Chunk4_1_checked, root1Node21Step3Chunk4_2_checked, root1Node21Step3Chunk4_3_checked, root1Node21Step3Chunk4_4_checked, root1Node21Step3Chunk4_5_checked, root1Node21Step3Chunk5_0_checked, root1Node21Step3Chunk5_1_checked, root1Node21Step3Chunk5_2_checked, root1Node21Step3Chunk5_3_checked, root1Node21Step3Chunk5_4_checked, root1Node21Step3Chunk5_5_checked, root1Node21Step3Chunk6_0_checked, root1Node21Step3Chunk6_1_checked, root1Node21Step3Chunk6_2_checked, root1Node21Step3Chunk6_3_checked, root1Node21Step3Chunk6_4_checked, root1Node21Step3Chunk6_5_checked, root1Node21Step3Chunk7_0_checked, root1Node21Step3Chunk7_1_checked, root1Node21Step3Chunk7_2_checked, root1Node21Step3Chunk7_3_checked, root1Node21Step3Chunk7_4_checked, root1Node21Step3Chunk7_5_checked, root1Node21Step3Chunk8_0_checked, root1Node21Step3Chunk8_1_checked, root1Node21Step3Chunk8_2_checked, root1Node21Step3Chunk8_3_checked, root1Node21Step3Chunk8_4_checked, root1Node21Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node22Domains0 : Domains 61 State := restrict root1Node21Domains3 0 (3,4)
def root1Node22Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,1),(2,3)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(0,0),(6,4)]
  | 12 => some [(1,2),(3,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3),(8,3)]
  | 18 => some [(1,5),(7,5)]
  | 19 => some [(0,3),(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0),(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(7,2)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(4,2),(7,0)]
  | 28 => some [(5,3),(8,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(5,1),(7,1),(8,1)]
  | 35 => some [(1,2),(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3),(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(5,0),(5,3),(8,3)]
  | 43 => some [(4,1),(8,1)]
  | 44 => some [(0,2),(6,5)]
  | 45 => some [(0,4),(1,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,0),(0,1),(6,4)]
  | 48 => some [(1,2),(6,2),(7,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(1,5),(3,5),(5,5),(7,5)]
  | 54 => some [(0,3),(1,0),(6,1)]
  | 55 => some [(2,1),(4,1),(8,1)]
  | 56 => some [(4,4),(5,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(1,3),(6,3)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | _ => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
theorem root1Node22Domains0_fast_eq : root1Node22Domains0 = expandDomains root1Node22Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node22Domains0 v = expandDomains root1Node22Domains0Fast v from by decide) v
def root1Node22Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(3,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(2,3)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(5,0),(8,0)]
  | 17 => [(4,5),(7,3),(8,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(0,0),(1,4),(6,4)]
  | 25 => [(0,5),(1,2),(7,2)]
  | 26 => [(7,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5),(7,5)]
  | 33 => [(0,3),(6,0),(6,1)]
  | 34 => [(5,1),(7,1),(8,1)]
  | 35 => [(1,2)]
  | 36 => [(7,4)]
  | 37 => [(1,3),(6,3)]
  | 38 => [(7,2),(8,2)]
  | 39 => [(4,0),(5,0),(8,0)]
  | 40 => [(4,5),(7,3)]
  | 41 => [(4,2),(7,0),(8,2)]
  | 42 => [(5,0),(5,3),(8,3)]
  | 43 => [(4,1),(8,1)]
  | 44 => [(0,2),(6,5)]
  | 45 => [(0,4),(1,1)]
  | 46 => [(5,1),(5,4)]
  | 47 => [(0,0),(0,1),(6,4)]
  | 48 => [(1,2),(6,2),(7,2)]
  | 49 => [(7,4),(8,4)]
  | 50 => [(5,2),(5,5),(8,5)]
  | 51 => [(7,0),(8,0)]
  | 52 => [(4,3),(8,3)]
  | 53 => [(1,5),(3,5),(5,5),(7,5)]
  | 54 => [(0,3),(1,0),(6,1)]
  | 55 => [(2,1),(4,1),(8,1)]
  | 56 => [(4,4),(5,4),(7,2),(8,4)]
  | 57 => [(1,4),(7,4)]
  | 58 => [(0,5),(1,3),(6,3)]
  | 59 => [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | _ => [(0,0),(1,3),(3,3),(5,3),(7,3)]
def root1Node22Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,3)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3),(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0),(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(7,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(5,1),(7,1),(8,1)]
  | 35 => some [(1,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3),(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(5,0),(5,3),(8,3)]
  | 43 => some [(4,1),(8,1)]
  | 44 => some [(0,2),(6,5)]
  | 45 => some [(0,4),(1,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,0),(0,1),(6,4)]
  | 48 => some [(1,2),(6,2),(7,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(1,5),(3,5),(5,5),(7,5)]
  | 54 => some [(0,3),(1,0),(6,1)]
  | 55 => some [(2,1),(4,1),(8,1)]
  | 56 => some [(4,4),(5,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(1,3),(6,3)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | _ => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
theorem root1Node22Domains1_fast_eq : root1Node22Domains1 = expandDomains root1Node22Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node22Domains1 v = expandDomains root1Node22Domains1Fast v from by decide) v
theorem root1Node22Step1Chunk0_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_0⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk0_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_1⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk0_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_2⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk0_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_3⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk0_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_4⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk0_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_5⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk1_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_0⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk1_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_1⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk1_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_2⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk1_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_3⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk1_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_4⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk1_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_5⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk2_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_0⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk2_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_1⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk2_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_2⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk2_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_3⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk2_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_4⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk2_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_5⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk3_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_0⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk3_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_1⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk3_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_2⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk3_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_3⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk3_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_4⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk3_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_5⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk4_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_0⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk4_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_1⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk4_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_2⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk4_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_3⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk4_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_4⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk4_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_5⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk5_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_0⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk5_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_1⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk5_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_2⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk5_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_3⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk5_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_4⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk5_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_5⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk6_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_0⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk6_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_1⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk6_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_2⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk6_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_3⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk6_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_4⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk6_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_5⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk7_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_0⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk7_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_1⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk7_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_2⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk7_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_3⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk7_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_4⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk7_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_5⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk8_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_0⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk8_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_1⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk8_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_2⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk8_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_3⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk8_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_4⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk8_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_5⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1_checked :
    checkReplacement table11 root1Node22Domains0 root1Node22Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node22Step1Chunk0_0_checked, root1Node22Step1Chunk0_1_checked, root1Node22Step1Chunk0_2_checked, root1Node22Step1Chunk0_3_checked, root1Node22Step1Chunk0_4_checked, root1Node22Step1Chunk0_5_checked, root1Node22Step1Chunk1_0_checked, root1Node22Step1Chunk1_1_checked, root1Node22Step1Chunk1_2_checked, root1Node22Step1Chunk1_3_checked, root1Node22Step1Chunk1_4_checked, root1Node22Step1Chunk1_5_checked, root1Node22Step1Chunk2_0_checked, root1Node22Step1Chunk2_1_checked, root1Node22Step1Chunk2_2_checked, root1Node22Step1Chunk2_3_checked, root1Node22Step1Chunk2_4_checked, root1Node22Step1Chunk2_5_checked, root1Node22Step1Chunk3_0_checked, root1Node22Step1Chunk3_1_checked, root1Node22Step1Chunk3_2_checked, root1Node22Step1Chunk3_3_checked, root1Node22Step1Chunk3_4_checked, root1Node22Step1Chunk3_5_checked, root1Node22Step1Chunk4_0_checked, root1Node22Step1Chunk4_1_checked, root1Node22Step1Chunk4_2_checked, root1Node22Step1Chunk4_3_checked, root1Node22Step1Chunk4_4_checked, root1Node22Step1Chunk4_5_checked, root1Node22Step1Chunk5_0_checked, root1Node22Step1Chunk5_1_checked, root1Node22Step1Chunk5_2_checked, root1Node22Step1Chunk5_3_checked, root1Node22Step1Chunk5_4_checked, root1Node22Step1Chunk5_5_checked, root1Node22Step1Chunk6_0_checked, root1Node22Step1Chunk6_1_checked, root1Node22Step1Chunk6_2_checked, root1Node22Step1Chunk6_3_checked, root1Node22Step1Chunk6_4_checked, root1Node22Step1Chunk6_5_checked, root1Node22Step1Chunk7_0_checked, root1Node22Step1Chunk7_1_checked, root1Node22Step1Chunk7_2_checked, root1Node22Step1Chunk7_3_checked, root1Node22Step1Chunk7_4_checked, root1Node22Step1Chunk7_5_checked, root1Node22Step1Chunk8_0_checked, root1Node22Step1Chunk8_1_checked, root1Node22Step1Chunk8_2_checked, root1Node22Step1Chunk8_3_checked, root1Node22Step1Chunk8_4_checked, root1Node22Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node23Domains0 : Domains 61 State := restrict root1Node22Domains1 16 (5,0)
def root1Node23Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,3)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5),(7,3),(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0),(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(7,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(5,1),(7,1),(8,1)]
  | 35 => some [(1,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3),(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(5,0),(5,3),(8,3)]
  | 43 => some [(4,1),(8,1)]
  | 44 => some [(0,2),(6,5)]
  | 45 => some [(0,4),(1,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,0),(0,1),(6,4)]
  | 48 => some [(1,2),(6,2),(7,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(1,5),(3,5),(5,5),(7,5)]
  | 54 => some [(0,3),(1,0),(6,1)]
  | 55 => some [(2,1),(4,1),(8,1)]
  | 56 => some [(4,4),(5,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(1,3),(6,3)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | _ => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
theorem root1Node23Domains0_fast_eq : root1Node23Domains0 = expandDomains root1Node23Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node23Domains0 v = expandDomains root1Node23Domains0Fast v from by decide) v
def root1Node23Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(3,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(2,3)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(0,0)]
  | 25 => [(7,2)]
  | 26 => [(7,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5)]
  | 33 => [(6,1)]
  | 34 => [(5,1)]
  | 35 => [(1,2)]
  | 36 => [(7,4)]
  | 37 => [(1,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(7,0)]
  | 42 => [(8,3)]
  | 43 => [(4,1),(8,1)]
  | 44 => [(0,2),(6,5)]
  | 45 => [(0,4)]
  | 46 => [(5,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(7,4)]
  | 50 => [(5,2),(5,5),(8,5)]
  | 51 => [(7,0),(8,0)]
  | 52 => [(4,3)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(4,1)]
  | 56 => [(4,4),(5,4),(7,2),(8,4)]
  | 57 => [(1,4),(7,4)]
  | 58 => [(0,5)]
  | 59 => [(2,0)]
  | _ => [(7,3)]
def root1Node23Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,3)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0)]
  | 25 => some [(7,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(5,1)]
  | 35 => some [(1,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(4,1),(8,1)]
  | 44 => some [(0,2),(6,5)]
  | 45 => some [(0,4)]
  | 46 => some [(5,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(4,1)]
  | 56 => some [(4,4),(5,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5)]
  | 59 => some [(2,0)]
  | _ => some [(7,3)]
theorem root1Node23Domains1_fast_eq : root1Node23Domains1 = expandDomains root1Node23Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node23Domains1 v = expandDomains root1Node23Domains1Fast v from by decide) v
theorem root1Node23Step1Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root1Node23Domains0 root1Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains0 root1Node23Domains1
    root1Node23Domains0Fast root1Node23Domains1Fast
    root1Node23Domains0_fast_eq root1Node23Domains1_fast_eq (by decide)
theorem root1Node23Step1_checked :
    checkReplacement table40 root1Node23Domains0 root1Node23Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node23Step1Chunk0_0_checked, root1Node23Step1Chunk0_1_checked, root1Node23Step1Chunk0_2_checked, root1Node23Step1Chunk0_3_checked, root1Node23Step1Chunk0_4_checked, root1Node23Step1Chunk0_5_checked, root1Node23Step1Chunk1_0_checked, root1Node23Step1Chunk1_1_checked, root1Node23Step1Chunk1_2_checked, root1Node23Step1Chunk1_3_checked, root1Node23Step1Chunk1_4_checked, root1Node23Step1Chunk1_5_checked, root1Node23Step1Chunk2_0_checked, root1Node23Step1Chunk2_1_checked, root1Node23Step1Chunk2_2_checked, root1Node23Step1Chunk2_3_checked, root1Node23Step1Chunk2_4_checked, root1Node23Step1Chunk2_5_checked, root1Node23Step1Chunk3_0_checked, root1Node23Step1Chunk3_1_checked, root1Node23Step1Chunk3_2_checked, root1Node23Step1Chunk3_3_checked, root1Node23Step1Chunk3_4_checked, root1Node23Step1Chunk3_5_checked, root1Node23Step1Chunk4_0_checked, root1Node23Step1Chunk4_1_checked, root1Node23Step1Chunk4_2_checked, root1Node23Step1Chunk4_3_checked, root1Node23Step1Chunk4_4_checked, root1Node23Step1Chunk4_5_checked, root1Node23Step1Chunk5_0_checked, root1Node23Step1Chunk5_1_checked, root1Node23Step1Chunk5_2_checked, root1Node23Step1Chunk5_3_checked, root1Node23Step1Chunk5_4_checked, root1Node23Step1Chunk5_5_checked, root1Node23Step1Chunk6_0_checked, root1Node23Step1Chunk6_1_checked, root1Node23Step1Chunk6_2_checked, root1Node23Step1Chunk6_3_checked, root1Node23Step1Chunk6_4_checked, root1Node23Step1Chunk6_5_checked, root1Node23Step1Chunk7_0_checked, root1Node23Step1Chunk7_1_checked, root1Node23Step1Chunk7_2_checked, root1Node23Step1Chunk7_3_checked, root1Node23Step1Chunk7_4_checked, root1Node23Step1Chunk7_5_checked, root1Node23Step1Chunk8_0_checked, root1Node23Step1Chunk8_1_checked, root1Node23Step1Chunk8_2_checked, root1Node23Step1Chunk8_3_checked, root1Node23Step1Chunk8_4_checked, root1Node23Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node23Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(3,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(2,3)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(0,0)]
  | 25 => [(7,2)]
  | 26 => [(7,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5)]
  | 33 => [(6,1)]
  | 34 => [(5,1)]
  | 35 => [(1,2)]
  | 36 => [(7,4)]
  | 37 => [(1,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(7,0)]
  | 42 => [(8,3)]
  | 43 => [(8,1)]
  | 44 => [(6,5)]
  | 45 => [(0,4)]
  | 46 => [(5,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(7,4)]
  | 50 => [(5,5)]
  | 51 => [(7,0)]
  | 52 => [(4,3)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(4,1)]
  | 56 => [(4,4)]
  | 57 => [(1,4)]
  | 58 => [(0,5)]
  | 59 => [(2,0)]
  | _ => [(7,3)]
def root1Node23Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,3)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0)]
  | 25 => some [(7,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(5,1)]
  | 35 => some [(1,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(8,1)]
  | 44 => some [(6,5)]
  | 45 => some [(0,4)]
  | 46 => some [(5,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,5)]
  | 51 => some [(7,0)]
  | 52 => some [(4,3)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(4,1)]
  | 56 => some [(4,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(2,0)]
  | _ => some [(7,3)]
theorem root1Node23Domains2_fast_eq : root1Node23Domains2 = expandDomains root1Node23Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node23Domains2 v = expandDomains root1Node23Domains2Fast v from by decide) v
theorem root1Node23Step2Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root1Node23Domains1 root1Node23Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node23Domains1 root1Node23Domains2
    root1Node23Domains1Fast root1Node23Domains2Fast
    root1Node23Domains1_fast_eq root1Node23Domains2_fast_eq (by decide)
theorem root1Node23Step2_checked :
    checkReplacement table36 root1Node23Domains1 root1Node23Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node23Step2Chunk0_0_checked, root1Node23Step2Chunk0_1_checked, root1Node23Step2Chunk0_2_checked, root1Node23Step2Chunk0_3_checked, root1Node23Step2Chunk0_4_checked, root1Node23Step2Chunk0_5_checked, root1Node23Step2Chunk1_0_checked, root1Node23Step2Chunk1_1_checked, root1Node23Step2Chunk1_2_checked, root1Node23Step2Chunk1_3_checked, root1Node23Step2Chunk1_4_checked, root1Node23Step2Chunk1_5_checked, root1Node23Step2Chunk2_0_checked, root1Node23Step2Chunk2_1_checked, root1Node23Step2Chunk2_2_checked, root1Node23Step2Chunk2_3_checked, root1Node23Step2Chunk2_4_checked, root1Node23Step2Chunk2_5_checked, root1Node23Step2Chunk3_0_checked, root1Node23Step2Chunk3_1_checked, root1Node23Step2Chunk3_2_checked, root1Node23Step2Chunk3_3_checked, root1Node23Step2Chunk3_4_checked, root1Node23Step2Chunk3_5_checked, root1Node23Step2Chunk4_0_checked, root1Node23Step2Chunk4_1_checked, root1Node23Step2Chunk4_2_checked, root1Node23Step2Chunk4_3_checked, root1Node23Step2Chunk4_4_checked, root1Node23Step2Chunk4_5_checked, root1Node23Step2Chunk5_0_checked, root1Node23Step2Chunk5_1_checked, root1Node23Step2Chunk5_2_checked, root1Node23Step2Chunk5_3_checked, root1Node23Step2Chunk5_4_checked, root1Node23Step2Chunk5_5_checked, root1Node23Step2Chunk6_0_checked, root1Node23Step2Chunk6_1_checked, root1Node23Step2Chunk6_2_checked, root1Node23Step2Chunk6_3_checked, root1Node23Step2Chunk6_4_checked, root1Node23Step2Chunk6_5_checked, root1Node23Step2Chunk7_0_checked, root1Node23Step2Chunk7_1_checked, root1Node23Step2Chunk7_2_checked, root1Node23Step2Chunk7_3_checked, root1Node23Step2Chunk7_4_checked, root1Node23Step2Chunk7_5_checked, root1Node23Step2Chunk8_0_checked, root1Node23Step2Chunk8_1_checked, root1Node23Step2Chunk8_2_checked, root1Node23Step2Chunk8_3_checked, root1Node23Step2Chunk8_4_checked, root1Node23Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root1Node23Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node23Domains2 (.output 10) = true := by decide
def root1Node24Domains0 : Domains 61 State := restrict root1Node22Domains1 16 (8,0)
def root1Node24Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,3)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(4,5),(7,3),(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0),(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(7,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(5,1),(7,1),(8,1)]
  | 35 => some [(1,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3),(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(5,0),(5,3),(8,3)]
  | 43 => some [(4,1),(8,1)]
  | 44 => some [(0,2),(6,5)]
  | 45 => some [(0,4),(1,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,0),(0,1),(6,4)]
  | 48 => some [(1,2),(6,2),(7,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(1,5),(3,5),(5,5),(7,5)]
  | 54 => some [(0,3),(1,0),(6,1)]
  | 55 => some [(2,1),(4,1),(8,1)]
  | 56 => some [(4,4),(5,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(1,3),(6,3)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | _ => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
theorem root1Node24Domains0_fast_eq : root1Node24Domains0 = expandDomains root1Node24Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node24Domains0 v = expandDomains root1Node24Domains0Fast v from by decide) v
def root1Node24Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(3,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(2,3)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(7,3),(8,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(1,4),(6,4)]
  | 25 => [(0,5),(1,2)]
  | 26 => [(7,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(0,3),(6,0)]
  | 34 => [(7,1),(8,1)]
  | 35 => [(1,2)]
  | 36 => [(7,4)]
  | 37 => [(1,3),(6,3)]
  | 38 => [(7,2),(8,2)]
  | 39 => [(4,0),(8,0)]
  | 40 => [(7,3)]
  | 41 => [(4,2),(8,2)]
  | 42 => [(5,0),(5,3)]
  | 43 => [(4,1),(8,1)]
  | 44 => [(0,2),(6,5)]
  | 45 => [(0,4),(1,1)]
  | 46 => [(5,1),(5,4)]
  | 47 => [(0,1),(6,4)]
  | 48 => [(1,2),(6,2)]
  | 49 => [(7,4),(8,4)]
  | 50 => [(5,2),(5,5),(8,5)]
  | 51 => [(7,0),(8,0)]
  | 52 => [(4,3),(8,3)]
  | 53 => [(3,5),(5,5),(7,5)]
  | 54 => [(0,3),(1,0)]
  | 55 => [(2,1),(4,1),(8,1)]
  | 56 => [(4,4),(5,4),(7,2),(8,4)]
  | 57 => [(1,4),(7,4)]
  | 58 => [(0,5),(1,3),(6,3)]
  | 59 => [(2,2),(2,4),(4,2),(4,4)]
  | _ => [(0,0),(1,3),(3,3),(5,3)]
def root1Node24Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,3)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3),(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4),(6,4)]
  | 25 => some [(0,5),(1,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3),(6,0)]
  | 34 => some [(7,1),(8,1)]
  | 35 => some [(1,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3),(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2),(8,2)]
  | 42 => some [(5,0),(5,3)]
  | 43 => some [(4,1),(8,1)]
  | 44 => some [(0,2),(6,5)]
  | 45 => some [(0,4),(1,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,1),(6,4)]
  | 48 => some [(1,2),(6,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(3,5),(5,5),(7,5)]
  | 54 => some [(0,3),(1,0)]
  | 55 => some [(2,1),(4,1),(8,1)]
  | 56 => some [(4,4),(5,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(1,3),(6,3)]
  | 59 => some [(2,2),(2,4),(4,2),(4,4)]
  | _ => some [(0,0),(1,3),(3,3),(5,3)]
theorem root1Node24Domains1_fast_eq : root1Node24Domains1 = expandDomains root1Node24Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node24Domains1 v = expandDomains root1Node24Domains1Fast v from by decide) v
theorem root1Node24Step1Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root1Node24Domains0 root1Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node24Domains0 root1Node24Domains1
    root1Node24Domains0Fast root1Node24Domains1Fast
    root1Node24Domains0_fast_eq root1Node24Domains1_fast_eq (by decide)
theorem root1Node24Step1_checked :
    checkReplacement table40 root1Node24Domains0 root1Node24Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node24Step1Chunk0_0_checked, root1Node24Step1Chunk0_1_checked, root1Node24Step1Chunk0_2_checked, root1Node24Step1Chunk0_3_checked, root1Node24Step1Chunk0_4_checked, root1Node24Step1Chunk0_5_checked, root1Node24Step1Chunk1_0_checked, root1Node24Step1Chunk1_1_checked, root1Node24Step1Chunk1_2_checked, root1Node24Step1Chunk1_3_checked, root1Node24Step1Chunk1_4_checked, root1Node24Step1Chunk1_5_checked, root1Node24Step1Chunk2_0_checked, root1Node24Step1Chunk2_1_checked, root1Node24Step1Chunk2_2_checked, root1Node24Step1Chunk2_3_checked, root1Node24Step1Chunk2_4_checked, root1Node24Step1Chunk2_5_checked, root1Node24Step1Chunk3_0_checked, root1Node24Step1Chunk3_1_checked, root1Node24Step1Chunk3_2_checked, root1Node24Step1Chunk3_3_checked, root1Node24Step1Chunk3_4_checked, root1Node24Step1Chunk3_5_checked, root1Node24Step1Chunk4_0_checked, root1Node24Step1Chunk4_1_checked, root1Node24Step1Chunk4_2_checked, root1Node24Step1Chunk4_3_checked, root1Node24Step1Chunk4_4_checked, root1Node24Step1Chunk4_5_checked, root1Node24Step1Chunk5_0_checked, root1Node24Step1Chunk5_1_checked, root1Node24Step1Chunk5_2_checked, root1Node24Step1Chunk5_3_checked, root1Node24Step1Chunk5_4_checked, root1Node24Step1Chunk5_5_checked, root1Node24Step1Chunk6_0_checked, root1Node24Step1Chunk6_1_checked, root1Node24Step1Chunk6_2_checked, root1Node24Step1Chunk6_3_checked, root1Node24Step1Chunk6_4_checked, root1Node24Step1Chunk6_5_checked, root1Node24Step1Chunk7_0_checked, root1Node24Step1Chunk7_1_checked, root1Node24Step1Chunk7_2_checked, root1Node24Step1Chunk7_3_checked, root1Node24Step1Chunk7_4_checked, root1Node24Step1Chunk7_5_checked, root1Node24Step1Chunk8_0_checked, root1Node24Step1Chunk8_1_checked, root1Node24Step1Chunk8_2_checked, root1Node24Step1Chunk8_3_checked, root1Node24Step1Chunk8_4_checked, root1Node24Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
