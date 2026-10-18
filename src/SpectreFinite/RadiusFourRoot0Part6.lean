module

public import SpectreFinite.RadiusFourRoot0Part5
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable23
public import SpectreFinite.RadiusFourTable26
public import SpectreFinite.RadiusFourTable38
public import SpectreFinite.RadiusFourTable39
public import SpectreFinite.RadiusFourTable5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node12Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(4,0),(7,0),(8,0)]
  | 1 => [(4,3),(7,3),(8,3)]
  | 2 => [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 3 => [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 4 => [(2,1),(2,5),(4,1),(4,5)]
  | 5 => [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 6 => [(0,1),(1,4),(7,4)]
  | 7 => [(0,5),(6,2),(6,3)]
  | 8 => [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 9 => [(0,0),(1,3),(3,3),(7,3)]
  | 10 => [(3,2),(5,2),(7,2)]
  | 11 => [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 12 => [(4,1),(7,5),(8,5)]
  | 13 => [(0,2),(1,0),(6,0)]
  | 14 => [(1,1),(3,1),(7,1)]
  | 15 => [(0,1),(1,5),(6,5)]
  | 16 => [(0,4),(6,1),(6,2)]
  | 17 => [(5,1),(5,4),(8,1),(8,4)]
  | 18 => [(4,0),(7,4),(8,0)]
  | 19 => [(1,3),(7,3)]
  | 20 => [(5,2),(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(1,0),(7,0)]
  | 24 => [(4,3),(7,1),(8,3)]
  | 25 => [(7,5),(8,5)]
  | 26 => [(5,1),(5,4),(8,1),(8,4)]
  | 27 => [(0,1),(6,4),(6,5)]
  | 28 => [(0,4),(1,2),(6,2)]
  | 29 => [(5,4),(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0),(7,4)]
  | 33 => [(1,3),(6,3),(7,3)]
  | 34 => [(4,2),(7,2),(8,2)]
  | 35 => [(5,5),(7,5),(8,5)]
  | 36 => [(0,3),(1,0),(7,0)]
  | 37 => [(4,3),(7,1),(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(4,1),(5,1),(8,1)]
  | 41 => [(0,1),(0,2),(6,5)]
  | 42 => [(0,4),(1,1),(6,2)]
  | 43 => [(4,2),(4,4),(8,2)]
  | 44 => [(1,4),(5,0),(5,3)]
  | 45 => [(0,5),(4,5),(5,5),(8,5)]
  | 46 => [(2,0),(7,0)]
  | 47 => [(7,3),(8,3)]
  | 48 => [(5,2),(5,5),(8,5)]
  | 49 => [(1,0),(3,0),(7,0),(8,0)]
  | 50 => [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 51 => [(0,0),(0,5),(6,0),(6,3)]
  | 52 => [(3,1),(4,4),(7,2)]
  | 53 => [(0,1),(1,4),(7,4)]
  | 54 => [(0,5),(1,3),(6,2),(6,3)]
  | 55 => [(4,4),(7,2),(8,2),(8,4)]
  | 56 => [(0,2),(1,5),(6,0),(8,2)]
  | 57 => [(1,1),(5,0),(6,1),(7,1)]
  | 58 => [(4,1),(4,5),(7,5),(8,1)]
  | 59 => [(0,2),(1,0),(6,0),(6,5)]
  | _ => [(0,4),(1,1),(7,1)]
def root0Node12Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(7,0),(8,0)]
  | 1 => some [(4,3),(7,3),(8,3)]
  | 2 => some [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 3 => some [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 4 => some [(2,1),(2,5),(4,1),(4,5)]
  | 5 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 6 => some [(0,1),(1,4),(7,4)]
  | 7 => some [(0,5),(6,2),(6,3)]
  | 8 => some [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 9 => some [(0,0),(1,3),(3,3),(7,3)]
  | 10 => some [(3,2),(5,2),(7,2)]
  | 11 => some [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 12 => some [(4,1),(7,5),(8,5)]
  | 13 => some [(0,2),(1,0),(6,0)]
  | 14 => some [(1,1),(3,1),(7,1)]
  | 15 => some [(0,1),(1,5),(6,5)]
  | 16 => some [(0,4),(6,1),(6,2)]
  | 17 => some [(5,1),(5,4),(8,1),(8,4)]
  | 18 => some [(4,0),(7,4),(8,0)]
  | 19 => some [(1,3),(7,3)]
  | 20 => some [(5,2),(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0),(7,0)]
  | 24 => some [(4,3),(7,1),(8,3)]
  | 25 => some [(7,5),(8,5)]
  | 26 => some [(5,1),(5,4),(8,1),(8,4)]
  | 27 => some [(0,1),(6,4),(6,5)]
  | 28 => some [(0,4),(1,2),(6,2)]
  | 29 => some [(5,4),(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0),(7,4)]
  | 33 => some [(1,3),(6,3),(7,3)]
  | 34 => some [(4,2),(7,2),(8,2)]
  | 35 => some [(5,5),(7,5),(8,5)]
  | 36 => some [(0,3),(1,0),(7,0)]
  | 37 => some [(4,3),(7,1),(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(4,1),(5,1),(8,1)]
  | 41 => some [(0,1),(0,2),(6,5)]
  | 42 => some [(0,4),(1,1),(6,2)]
  | 43 => some [(4,2),(4,4),(8,2)]
  | 44 => some [(1,4),(5,0),(5,3)]
  | 45 => some [(0,5),(4,5),(5,5),(8,5)]
  | 46 => some [(2,0),(7,0)]
  | 47 => some [(7,3),(8,3)]
  | 48 => some [(5,2),(5,5),(8,5)]
  | 49 => some [(1,0),(3,0),(7,0),(8,0)]
  | 50 => some [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 51 => some [(0,0),(0,5),(6,0),(6,3)]
  | 52 => some [(3,1),(4,4),(7,2)]
  | 53 => some [(0,1),(1,4),(7,4)]
  | 54 => some [(0,5),(1,3),(6,2),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2),(8,4)]
  | 56 => some [(0,2),(1,5),(6,0),(8,2)]
  | 57 => some [(1,1),(5,0),(6,1),(7,1)]
  | 58 => some [(4,1),(4,5),(7,5),(8,1)]
  | 59 => some [(0,2),(1,0),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root0Node12Domains3_fast_eq : root0Node12Domains3 = expandDomains root0Node12Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node12Domains3 v = expandDomains root0Node12Domains3Fast v from by decide) v
theorem root0Node12Step3Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root0Node12Domains2 root0Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node12Domains2 root0Node12Domains3
    root0Node12Domains2Fast root0Node12Domains3Fast
    root0Node12Domains2_fast_eq root0Node12Domains3_fast_eq (by decide)
theorem root0Node12Step3_checked :
    checkReplacement table26 root0Node12Domains2 root0Node12Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node12Step3Chunk0_0_checked, root0Node12Step3Chunk0_1_checked, root0Node12Step3Chunk0_2_checked, root0Node12Step3Chunk0_3_checked, root0Node12Step3Chunk0_4_checked, root0Node12Step3Chunk0_5_checked, root0Node12Step3Chunk1_0_checked, root0Node12Step3Chunk1_1_checked, root0Node12Step3Chunk1_2_checked, root0Node12Step3Chunk1_3_checked, root0Node12Step3Chunk1_4_checked, root0Node12Step3Chunk1_5_checked, root0Node12Step3Chunk2_0_checked, root0Node12Step3Chunk2_1_checked, root0Node12Step3Chunk2_2_checked, root0Node12Step3Chunk2_3_checked, root0Node12Step3Chunk2_4_checked, root0Node12Step3Chunk2_5_checked, root0Node12Step3Chunk3_0_checked, root0Node12Step3Chunk3_1_checked, root0Node12Step3Chunk3_2_checked, root0Node12Step3Chunk3_3_checked, root0Node12Step3Chunk3_4_checked, root0Node12Step3Chunk3_5_checked, root0Node12Step3Chunk4_0_checked, root0Node12Step3Chunk4_1_checked, root0Node12Step3Chunk4_2_checked, root0Node12Step3Chunk4_3_checked, root0Node12Step3Chunk4_4_checked, root0Node12Step3Chunk4_5_checked, root0Node12Step3Chunk5_0_checked, root0Node12Step3Chunk5_1_checked, root0Node12Step3Chunk5_2_checked, root0Node12Step3Chunk5_3_checked, root0Node12Step3Chunk5_4_checked, root0Node12Step3Chunk5_5_checked, root0Node12Step3Chunk6_0_checked, root0Node12Step3Chunk6_1_checked, root0Node12Step3Chunk6_2_checked, root0Node12Step3Chunk6_3_checked, root0Node12Step3Chunk6_4_checked, root0Node12Step3Chunk6_5_checked, root0Node12Step3Chunk7_0_checked, root0Node12Step3Chunk7_1_checked, root0Node12Step3Chunk7_2_checked, root0Node12Step3Chunk7_3_checked, root0Node12Step3Chunk7_4_checked, root0Node12Step3Chunk7_5_checked, root0Node12Step3Chunk8_0_checked, root0Node12Step3Chunk8_1_checked, root0Node12Step3Chunk8_2_checked, root0Node12Step3Chunk8_3_checked, root0Node12Step3Chunk8_4_checked, root0Node12Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node13Domains0 : Domains 61 State := restrict root0Node12Domains3 19 (1,3)
def root0Node13Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(7,0),(8,0)]
  | 1 => some [(4,3),(7,3),(8,3)]
  | 2 => some [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 3 => some [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 4 => some [(2,1),(2,5),(4,1),(4,5)]
  | 5 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 6 => some [(0,1),(1,4),(7,4)]
  | 7 => some [(0,5),(6,2),(6,3)]
  | 8 => some [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 9 => some [(0,0),(1,3),(3,3),(7,3)]
  | 10 => some [(3,2),(5,2),(7,2)]
  | 11 => some [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 12 => some [(4,1),(7,5),(8,5)]
  | 13 => some [(0,2),(1,0),(6,0)]
  | 14 => some [(1,1),(3,1),(7,1)]
  | 15 => some [(0,1),(1,5),(6,5)]
  | 16 => some [(0,4),(6,1),(6,2)]
  | 17 => some [(5,1),(5,4),(8,1),(8,4)]
  | 18 => some [(4,0),(7,4),(8,0)]
  | 19 => some [(1,3)]
  | 20 => some [(5,2),(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0),(7,0)]
  | 24 => some [(4,3),(7,1),(8,3)]
  | 25 => some [(7,5),(8,5)]
  | 26 => some [(5,1),(5,4),(8,1),(8,4)]
  | 27 => some [(0,1),(6,4),(6,5)]
  | 28 => some [(0,4),(1,2),(6,2)]
  | 29 => some [(5,4),(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0),(7,4)]
  | 33 => some [(1,3),(6,3),(7,3)]
  | 34 => some [(4,2),(7,2),(8,2)]
  | 35 => some [(5,5),(7,5),(8,5)]
  | 36 => some [(0,3),(1,0),(7,0)]
  | 37 => some [(4,3),(7,1),(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(4,1),(5,1),(8,1)]
  | 41 => some [(0,1),(0,2),(6,5)]
  | 42 => some [(0,4),(1,1),(6,2)]
  | 43 => some [(4,2),(4,4),(8,2)]
  | 44 => some [(1,4),(5,0),(5,3)]
  | 45 => some [(0,5),(4,5),(5,5),(8,5)]
  | 46 => some [(2,0),(7,0)]
  | 47 => some [(7,3),(8,3)]
  | 48 => some [(5,2),(5,5),(8,5)]
  | 49 => some [(1,0),(3,0),(7,0),(8,0)]
  | 50 => some [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 51 => some [(0,0),(0,5),(6,0),(6,3)]
  | 52 => some [(3,1),(4,4),(7,2)]
  | 53 => some [(0,1),(1,4),(7,4)]
  | 54 => some [(0,5),(1,3),(6,2),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2),(8,4)]
  | 56 => some [(0,2),(1,5),(6,0),(8,2)]
  | 57 => some [(1,1),(5,0),(6,1),(7,1)]
  | 58 => some [(4,1),(4,5),(7,5),(8,1)]
  | 59 => some [(0,2),(1,0),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root0Node13Domains0_fast_eq : root0Node13Domains0 = expandDomains root0Node13Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node13Domains0 v = expandDomains root0Node13Domains0Fast v from by decide) v
def root0Node13Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(4,0),(7,0),(8,0)]
  | 1 => [(4,3),(7,3),(8,3)]
  | 2 => [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 3 => [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 4 => [(2,1),(2,5),(4,1),(4,5)]
  | 5 => [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 6 => [(0,1),(1,4),(7,4)]
  | 7 => [(0,5),(6,2),(6,3)]
  | 8 => [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 9 => [(0,0),(1,3),(3,3),(7,3)]
  | 10 => [(3,2),(5,2),(7,2)]
  | 11 => [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 12 => [(7,5),(8,5)]
  | 13 => [(1,0),(6,0)]
  | 14 => [(7,1)]
  | 15 => [(1,5)]
  | 16 => [(0,4),(6,1),(6,2)]
  | 17 => [(5,1),(5,4),(8,1),(8,4)]
  | 18 => [(4,0),(7,4),(8,0)]
  | 19 => [(1,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(7,0)]
  | 24 => [(4,3),(7,1),(8,3)]
  | 25 => [(7,5),(8,5)]
  | 26 => [(5,1),(5,4),(8,1),(8,4)]
  | 27 => [(6,5)]
  | 28 => [(0,4)]
  | 29 => [(5,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(7,4)]
  | 33 => [(1,3),(6,3),(7,3)]
  | 34 => [(4,2),(7,2),(8,2)]
  | 35 => [(5,5)]
  | 36 => [(7,0)]
  | 37 => [(4,3)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(4,1)]
  | 41 => [(0,2)]
  | 42 => [(0,4),(1,1),(6,2)]
  | 43 => [(4,4)]
  | 44 => [(1,4)]
  | 45 => [(0,5)]
  | 46 => [(2,0)]
  | 47 => [(7,3)]
  | 48 => [(5,2)]
  | 49 => [(1,0),(3,0),(7,0),(8,0)]
  | 50 => [(7,5)]
  | 51 => [(6,0)]
  | 52 => [(3,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(4,4),(7,2),(8,2),(8,4)]
  | 56 => [(8,2)]
  | 57 => [(5,0)]
  | 58 => [(4,5)]
  | 59 => [(1,0)]
  | _ => [(0,4),(1,1),(7,1)]
def root0Node13Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(7,0),(8,0)]
  | 1 => some [(4,3),(7,3),(8,3)]
  | 2 => some [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 3 => some [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 4 => some [(2,1),(2,5),(4,1),(4,5)]
  | 5 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 6 => some [(0,1),(1,4),(7,4)]
  | 7 => some [(0,5),(6,2),(6,3)]
  | 8 => some [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 9 => some [(0,0),(1,3),(3,3),(7,3)]
  | 10 => some [(3,2),(5,2),(7,2)]
  | 11 => some [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 12 => some [(7,5),(8,5)]
  | 13 => some [(1,0),(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,5)]
  | 16 => some [(0,4),(6,1),(6,2)]
  | 17 => some [(5,1),(5,4),(8,1),(8,4)]
  | 18 => some [(4,0),(7,4),(8,0)]
  | 19 => some [(1,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(4,3),(7,1),(8,3)]
  | 25 => some [(7,5),(8,5)]
  | 26 => some [(5,1),(5,4),(8,1),(8,4)]
  | 27 => some [(6,5)]
  | 28 => some [(0,4)]
  | 29 => some [(5,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(1,3),(6,3),(7,3)]
  | 34 => some [(4,2),(7,2),(8,2)]
  | 35 => some [(5,5)]
  | 36 => some [(7,0)]
  | 37 => some [(4,3)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(4,1)]
  | 41 => some [(0,2)]
  | 42 => some [(0,4),(1,1),(6,2)]
  | 43 => some [(4,4)]
  | 44 => some [(1,4)]
  | 45 => some [(0,5)]
  | 46 => some [(2,0)]
  | 47 => some [(7,3)]
  | 48 => some [(5,2)]
  | 49 => some [(1,0),(3,0),(7,0),(8,0)]
  | 50 => some [(7,5)]
  | 51 => some [(6,0)]
  | 52 => some [(3,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(4,4),(7,2),(8,2),(8,4)]
  | 56 => some [(8,2)]
  | 57 => some [(5,0)]
  | 58 => some [(4,5)]
  | 59 => some [(1,0)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root0Node13Domains1_fast_eq : root0Node13Domains1 = expandDomains root0Node13Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node13Domains1 v = expandDomains root0Node13Domains1Fast v from by decide) v
theorem root0Node13Step1Chunk0_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_0⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk0_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_1⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk0_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_2⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk0_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_3⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk0_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_4⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk0_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_5⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk1_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_0⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk1_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_1⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk1_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_2⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk1_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_3⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk1_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_4⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk1_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_5⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk2_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_0⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk2_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_1⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk2_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_2⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk2_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_3⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk2_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_4⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk2_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_5⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk3_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_0⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk3_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_1⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk3_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_2⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk3_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_3⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk3_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_4⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk3_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_5⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk4_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_0⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk4_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_1⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk4_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_2⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk4_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_3⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk4_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_4⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk4_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_5⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk5_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_0⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk5_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_1⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk5_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_2⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk5_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_3⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk5_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_4⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk5_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_5⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk6_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_0⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk6_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_1⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk6_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_2⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk6_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_3⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk6_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_4⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk6_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_5⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk7_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_0⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk7_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_1⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk7_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_2⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk7_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_3⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk7_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_4⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk7_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_5⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk8_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_0⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk8_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_1⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk8_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_2⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk8_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_3⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk8_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_4⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1Chunk8_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_5⟩
      root0Node13Domains0 root0Node13Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains0 root0Node13Domains1
    root0Node13Domains0Fast root0Node13Domains1Fast
    root0Node13Domains0_fast_eq root0Node13Domains1_fast_eq (by decide)
theorem root0Node13Step1_checked :
    checkReplacement table38 root0Node13Domains0 root0Node13Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node13Step1Chunk0_0_checked, root0Node13Step1Chunk0_1_checked, root0Node13Step1Chunk0_2_checked, root0Node13Step1Chunk0_3_checked, root0Node13Step1Chunk0_4_checked, root0Node13Step1Chunk0_5_checked, root0Node13Step1Chunk1_0_checked, root0Node13Step1Chunk1_1_checked, root0Node13Step1Chunk1_2_checked, root0Node13Step1Chunk1_3_checked, root0Node13Step1Chunk1_4_checked, root0Node13Step1Chunk1_5_checked, root0Node13Step1Chunk2_0_checked, root0Node13Step1Chunk2_1_checked, root0Node13Step1Chunk2_2_checked, root0Node13Step1Chunk2_3_checked, root0Node13Step1Chunk2_4_checked, root0Node13Step1Chunk2_5_checked, root0Node13Step1Chunk3_0_checked, root0Node13Step1Chunk3_1_checked, root0Node13Step1Chunk3_2_checked, root0Node13Step1Chunk3_3_checked, root0Node13Step1Chunk3_4_checked, root0Node13Step1Chunk3_5_checked, root0Node13Step1Chunk4_0_checked, root0Node13Step1Chunk4_1_checked, root0Node13Step1Chunk4_2_checked, root0Node13Step1Chunk4_3_checked, root0Node13Step1Chunk4_4_checked, root0Node13Step1Chunk4_5_checked, root0Node13Step1Chunk5_0_checked, root0Node13Step1Chunk5_1_checked, root0Node13Step1Chunk5_2_checked, root0Node13Step1Chunk5_3_checked, root0Node13Step1Chunk5_4_checked, root0Node13Step1Chunk5_5_checked, root0Node13Step1Chunk6_0_checked, root0Node13Step1Chunk6_1_checked, root0Node13Step1Chunk6_2_checked, root0Node13Step1Chunk6_3_checked, root0Node13Step1Chunk6_4_checked, root0Node13Step1Chunk6_5_checked, root0Node13Step1Chunk7_0_checked, root0Node13Step1Chunk7_1_checked, root0Node13Step1Chunk7_2_checked, root0Node13Step1Chunk7_3_checked, root0Node13Step1Chunk7_4_checked, root0Node13Step1Chunk7_5_checked, root0Node13Step1Chunk8_0_checked, root0Node13Step1Chunk8_1_checked, root0Node13Step1Chunk8_2_checked, root0Node13Step1Chunk8_3_checked, root0Node13Step1Chunk8_4_checked, root0Node13Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node13Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(4,0),(7,0),(8,0)]
  | 1 => [(4,3),(7,3),(8,3)]
  | 2 => [(5,2),(5,5),(8,2)]
  | 3 => [(1,0),(3,0),(5,0)]
  | 4 => [(2,1),(2,5),(4,5)]
  | 5 => [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 6 => [(0,1),(1,4),(7,4)]
  | 7 => [(0,5),(6,2)]
  | 8 => [(4,4),(8,4)]
  | 9 => [(0,0)]
  | 10 => [(3,2),(7,2)]
  | 11 => [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 12 => [(7,5),(8,5)]
  | 13 => [(1,0),(6,0)]
  | 14 => [(7,1)]
  | 15 => [(1,5)]
  | 16 => [(6,1)]
  | 17 => [(5,1),(8,1)]
  | 18 => [(4,0),(7,4),(8,0)]
  | 19 => [(1,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(7,0)]
  | 24 => [(8,3)]
  | 25 => [(8,5)]
  | 26 => [(5,1),(5,4),(8,1),(8,4)]
  | 27 => [(6,5)]
  | 28 => [(0,4)]
  | 29 => [(5,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(7,4)]
  | 33 => [(6,3)]
  | 34 => [(7,2)]
  | 35 => [(5,5)]
  | 36 => [(7,0)]
  | 37 => [(4,3)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(4,1)]
  | 41 => [(0,2)]
  | 42 => [(1,1)]
  | 43 => [(4,4)]
  | 44 => [(1,4)]
  | 45 => [(0,5)]
  | 46 => [(2,0)]
  | 47 => [(7,3)]
  | 48 => [(5,2)]
  | 49 => [(8,0)]
  | 50 => [(7,5)]
  | 51 => [(6,0)]
  | 52 => [(3,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(4,4),(7,2),(8,2),(8,4)]
  | 56 => [(8,2)]
  | 57 => [(5,0)]
  | 58 => [(4,5)]
  | 59 => [(1,0)]
  | _ => [(0,4),(1,1),(7,1)]
def root0Node13Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(7,0),(8,0)]
  | 1 => some [(4,3),(7,3),(8,3)]
  | 2 => some [(5,2),(5,5),(8,2)]
  | 3 => some [(1,0),(3,0),(5,0)]
  | 4 => some [(2,1),(2,5),(4,5)]
  | 5 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 6 => some [(0,1),(1,4),(7,4)]
  | 7 => some [(0,5),(6,2)]
  | 8 => some [(4,4),(8,4)]
  | 9 => some [(0,0)]
  | 10 => some [(3,2),(7,2)]
  | 11 => some [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 12 => some [(7,5),(8,5)]
  | 13 => some [(1,0),(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(5,1),(8,1)]
  | 18 => some [(4,0),(7,4),(8,0)]
  | 19 => some [(1,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(8,3)]
  | 25 => some [(8,5)]
  | 26 => some [(5,1),(5,4),(8,1),(8,4)]
  | 27 => some [(6,5)]
  | 28 => some [(0,4)]
  | 29 => some [(5,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(6,3)]
  | 34 => some [(7,2)]
  | 35 => some [(5,5)]
  | 36 => some [(7,0)]
  | 37 => some [(4,3)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(4,1)]
  | 41 => some [(0,2)]
  | 42 => some [(1,1)]
  | 43 => some [(4,4)]
  | 44 => some [(1,4)]
  | 45 => some [(0,5)]
  | 46 => some [(2,0)]
  | 47 => some [(7,3)]
  | 48 => some [(5,2)]
  | 49 => some [(8,0)]
  | 50 => some [(7,5)]
  | 51 => some [(6,0)]
  | 52 => some [(3,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(4,4),(7,2),(8,2),(8,4)]
  | 56 => some [(8,2)]
  | 57 => some [(5,0)]
  | 58 => some [(4,5)]
  | 59 => some [(1,0)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root0Node13Domains2_fast_eq : root0Node13Domains2 = expandDomains root0Node13Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node13Domains2 v = expandDomains root0Node13Domains2Fast v from by decide) v
theorem root0Node13Step2Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root0Node13Domains1 root0Node13Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains1 root0Node13Domains2
    root0Node13Domains1Fast root0Node13Domains2Fast
    root0Node13Domains1_fast_eq root0Node13Domains2_fast_eq (by decide)
theorem root0Node13Step2_checked :
    checkReplacement table23 root0Node13Domains1 root0Node13Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node13Step2Chunk0_0_checked, root0Node13Step2Chunk0_1_checked, root0Node13Step2Chunk0_2_checked, root0Node13Step2Chunk0_3_checked, root0Node13Step2Chunk0_4_checked, root0Node13Step2Chunk0_5_checked, root0Node13Step2Chunk1_0_checked, root0Node13Step2Chunk1_1_checked, root0Node13Step2Chunk1_2_checked, root0Node13Step2Chunk1_3_checked, root0Node13Step2Chunk1_4_checked, root0Node13Step2Chunk1_5_checked, root0Node13Step2Chunk2_0_checked, root0Node13Step2Chunk2_1_checked, root0Node13Step2Chunk2_2_checked, root0Node13Step2Chunk2_3_checked, root0Node13Step2Chunk2_4_checked, root0Node13Step2Chunk2_5_checked, root0Node13Step2Chunk3_0_checked, root0Node13Step2Chunk3_1_checked, root0Node13Step2Chunk3_2_checked, root0Node13Step2Chunk3_3_checked, root0Node13Step2Chunk3_4_checked, root0Node13Step2Chunk3_5_checked, root0Node13Step2Chunk4_0_checked, root0Node13Step2Chunk4_1_checked, root0Node13Step2Chunk4_2_checked, root0Node13Step2Chunk4_3_checked, root0Node13Step2Chunk4_4_checked, root0Node13Step2Chunk4_5_checked, root0Node13Step2Chunk5_0_checked, root0Node13Step2Chunk5_1_checked, root0Node13Step2Chunk5_2_checked, root0Node13Step2Chunk5_3_checked, root0Node13Step2Chunk5_4_checked, root0Node13Step2Chunk5_5_checked, root0Node13Step2Chunk6_0_checked, root0Node13Step2Chunk6_1_checked, root0Node13Step2Chunk6_2_checked, root0Node13Step2Chunk6_3_checked, root0Node13Step2Chunk6_4_checked, root0Node13Step2Chunk6_5_checked, root0Node13Step2Chunk7_0_checked, root0Node13Step2Chunk7_1_checked, root0Node13Step2Chunk7_2_checked, root0Node13Step2Chunk7_3_checked, root0Node13Step2Chunk7_4_checked, root0Node13Step2Chunk7_5_checked, root0Node13Step2Chunk8_0_checked, root0Node13Step2Chunk8_1_checked, root0Node13Step2Chunk8_2_checked, root0Node13Step2Chunk8_3_checked, root0Node13Step2Chunk8_4_checked, root0Node13Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node13Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(4,0),(8,0)]
  | 1 => [(7,3),(8,3)]
  | 2 => [(5,2),(5,5),(8,2)]
  | 3 => [(1,0),(3,0),(5,0)]
  | 4 => [(2,1),(2,5),(4,5)]
  | 5 => [(5,1),(5,4)]
  | 6 => [(0,1),(1,4)]
  | 7 => [(0,5),(6,2)]
  | 8 => [(4,4),(8,4)]
  | 9 => [(0,0)]
  | 10 => [(3,2),(7,2)]
  | 11 => [(4,3),(5,3),(8,3)]
  | 12 => [(7,5),(8,5)]
  | 13 => [(1,0),(6,0)]
  | 14 => [(7,1)]
  | 15 => [(1,5)]
  | 16 => [(6,1)]
  | 17 => [(5,1),(8,1)]
  | 18 => [(7,4)]
  | 19 => [(1,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(7,0)]
  | 24 => [(8,3)]
  | 25 => [(8,5)]
  | 26 => [(8,1)]
  | 27 => [(6,5)]
  | 28 => [(0,4)]
  | 29 => [(5,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(7,4)]
  | 33 => [(6,3)]
  | 34 => [(7,2)]
  | 35 => [(5,5)]
  | 36 => [(7,0)]
  | 37 => [(4,3)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(4,1)]
  | 41 => [(0,2)]
  | 42 => [(1,1)]
  | 43 => [(4,4)]
  | 44 => [(1,4)]
  | 45 => [(0,5)]
  | 46 => [(2,0)]
  | 47 => [(7,3)]
  | 48 => [(5,2)]
  | 49 => [(8,0)]
  | 50 => [(7,5)]
  | 51 => [(6,0)]
  | 52 => [(3,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(4,4),(7,2),(8,2),(8,4)]
  | 56 => [(8,2)]
  | 57 => [(5,0)]
  | 58 => [(4,5)]
  | 59 => [(1,0)]
  | _ => [(0,4),(1,1),(7,1)]
def root0Node13Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(8,0)]
  | 1 => some [(7,3),(8,3)]
  | 2 => some [(5,2),(5,5),(8,2)]
  | 3 => some [(1,0),(3,0),(5,0)]
  | 4 => some [(2,1),(2,5),(4,5)]
  | 5 => some [(5,1),(5,4)]
  | 6 => some [(0,1),(1,4)]
  | 7 => some [(0,5),(6,2)]
  | 8 => some [(4,4),(8,4)]
  | 9 => some [(0,0)]
  | 10 => some [(3,2),(7,2)]
  | 11 => some [(4,3),(5,3),(8,3)]
  | 12 => some [(7,5),(8,5)]
  | 13 => some [(1,0),(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(5,1),(8,1)]
  | 18 => some [(7,4)]
  | 19 => some [(1,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(8,3)]
  | 25 => some [(8,5)]
  | 26 => some [(8,1)]
  | 27 => some [(6,5)]
  | 28 => some [(0,4)]
  | 29 => some [(5,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(6,3)]
  | 34 => some [(7,2)]
  | 35 => some [(5,5)]
  | 36 => some [(7,0)]
  | 37 => some [(4,3)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(4,1)]
  | 41 => some [(0,2)]
  | 42 => some [(1,1)]
  | 43 => some [(4,4)]
  | 44 => some [(1,4)]
  | 45 => some [(0,5)]
  | 46 => some [(2,0)]
  | 47 => some [(7,3)]
  | 48 => some [(5,2)]
  | 49 => some [(8,0)]
  | 50 => some [(7,5)]
  | 51 => some [(6,0)]
  | 52 => some [(3,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(4,4),(7,2),(8,2),(8,4)]
  | 56 => some [(8,2)]
  | 57 => some [(5,0)]
  | 58 => some [(4,5)]
  | 59 => some [(1,0)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root0Node13Domains3_fast_eq : root0Node13Domains3 = expandDomains root0Node13Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node13Domains3 v = expandDomains root0Node13Domains3Fast v from by decide) v
theorem root0Node13Step3Chunk0_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_0⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk0_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_1⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk0_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_2⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk0_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_3⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk0_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_4⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk0_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_5⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk1_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_0⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk1_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_1⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk1_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_2⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk1_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_3⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk1_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_4⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk1_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_5⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk2_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_0⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk2_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_1⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk2_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_2⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk2_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_3⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk2_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_4⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk2_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_5⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk3_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_0⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk3_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_1⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk3_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_2⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk3_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_3⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk3_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_4⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk3_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_5⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk4_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_0⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk4_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_1⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk4_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_2⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk4_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_3⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk4_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_4⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk4_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_5⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk5_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_0⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk5_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_1⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk5_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_2⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk5_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_3⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk5_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_4⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk5_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_5⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk6_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_0⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk6_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_1⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk6_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_2⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk6_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_3⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk6_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_4⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk6_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_5⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk7_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_0⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk7_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_1⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk7_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_2⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk7_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_3⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk7_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_4⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk7_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_5⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk8_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_0⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk8_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_1⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk8_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_2⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk8_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_3⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk8_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_4⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3Chunk8_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_5⟩
      root0Node13Domains2 root0Node13Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains2 root0Node13Domains3
    root0Node13Domains2Fast root0Node13Domains3Fast
    root0Node13Domains2_fast_eq root0Node13Domains3_fast_eq (by decide)
theorem root0Node13Step3_checked :
    checkReplacement table5 root0Node13Domains2 root0Node13Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node13Step3Chunk0_0_checked, root0Node13Step3Chunk0_1_checked, root0Node13Step3Chunk0_2_checked, root0Node13Step3Chunk0_3_checked, root0Node13Step3Chunk0_4_checked, root0Node13Step3Chunk0_5_checked, root0Node13Step3Chunk1_0_checked, root0Node13Step3Chunk1_1_checked, root0Node13Step3Chunk1_2_checked, root0Node13Step3Chunk1_3_checked, root0Node13Step3Chunk1_4_checked, root0Node13Step3Chunk1_5_checked, root0Node13Step3Chunk2_0_checked, root0Node13Step3Chunk2_1_checked, root0Node13Step3Chunk2_2_checked, root0Node13Step3Chunk2_3_checked, root0Node13Step3Chunk2_4_checked, root0Node13Step3Chunk2_5_checked, root0Node13Step3Chunk3_0_checked, root0Node13Step3Chunk3_1_checked, root0Node13Step3Chunk3_2_checked, root0Node13Step3Chunk3_3_checked, root0Node13Step3Chunk3_4_checked, root0Node13Step3Chunk3_5_checked, root0Node13Step3Chunk4_0_checked, root0Node13Step3Chunk4_1_checked, root0Node13Step3Chunk4_2_checked, root0Node13Step3Chunk4_3_checked, root0Node13Step3Chunk4_4_checked, root0Node13Step3Chunk4_5_checked, root0Node13Step3Chunk5_0_checked, root0Node13Step3Chunk5_1_checked, root0Node13Step3Chunk5_2_checked, root0Node13Step3Chunk5_3_checked, root0Node13Step3Chunk5_4_checked, root0Node13Step3Chunk5_5_checked, root0Node13Step3Chunk6_0_checked, root0Node13Step3Chunk6_1_checked, root0Node13Step3Chunk6_2_checked, root0Node13Step3Chunk6_3_checked, root0Node13Step3Chunk6_4_checked, root0Node13Step3Chunk6_5_checked, root0Node13Step3Chunk7_0_checked, root0Node13Step3Chunk7_1_checked, root0Node13Step3Chunk7_2_checked, root0Node13Step3Chunk7_3_checked, root0Node13Step3Chunk7_4_checked, root0Node13Step3Chunk7_5_checked, root0Node13Step3Chunk8_0_checked, root0Node13Step3Chunk8_1_checked, root0Node13Step3Chunk8_2_checked, root0Node13Step3Chunk8_3_checked, root0Node13Step3Chunk8_4_checked, root0Node13Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node13Domains4 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(4,0),(8,0)]
  | 1 => [(7,3),(8,3)]
  | 2 => [(5,2),(5,5),(8,2)]
  | 3 => [(1,0),(3,0),(5,0)]
  | 4 => [(2,1),(2,5),(4,5)]
  | 5 => [(5,1),(5,4)]
  | 6 => [(0,1),(1,4)]
  | 7 => [(0,5),(6,2)]
  | 8 => [(4,4),(8,4)]
  | 9 => [(0,0)]
  | 10 => [(3,2),(7,2)]
  | 11 => [(4,3),(5,3),(8,3)]
  | 12 => [(7,5),(8,5)]
  | 13 => [(1,0),(6,0)]
  | 14 => [(7,1)]
  | 15 => [(1,5)]
  | 16 => [(6,1)]
  | 17 => [(5,1),(8,1)]
  | 18 => [(7,4)]
  | 19 => [(1,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(7,0)]
  | 24 => [(8,3)]
  | 25 => [(8,5)]
  | 26 => [(8,1)]
  | 27 => [(6,5)]
  | 28 => [(0,4)]
  | 29 => [(5,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(7,4)]
  | 33 => [(6,3)]
  | 34 => [(7,2)]
  | 35 => [(5,5)]
  | 36 => [(7,0)]
  | 37 => [(4,3)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(4,1)]
  | 41 => [(0,2)]
  | 42 => [(1,1)]
  | 43 => [(4,4)]
  | 44 => [(1,4)]
  | 45 => [(0,5)]
  | 46 => [(2,0)]
  | 47 => [(7,3)]
  | 48 => [(5,2)]
  | 49 => [(8,0)]
  | 50 => [(7,5)]
  | 51 => [(6,0)]
  | 52 => [(3,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(8,2)]
  | 57 => [(5,0)]
  | 58 => [(4,5)]
  | 59 => [(1,0)]
  | _ => [(7,1)]
def root0Node13Domains4Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(8,0)]
  | 1 => some [(7,3),(8,3)]
  | 2 => some [(5,2),(5,5),(8,2)]
  | 3 => some [(1,0),(3,0),(5,0)]
  | 4 => some [(2,1),(2,5),(4,5)]
  | 5 => some [(5,1),(5,4)]
  | 6 => some [(0,1),(1,4)]
  | 7 => some [(0,5),(6,2)]
  | 8 => some [(4,4),(8,4)]
  | 9 => some [(0,0)]
  | 10 => some [(3,2),(7,2)]
  | 11 => some [(4,3),(5,3),(8,3)]
  | 12 => some [(7,5),(8,5)]
  | 13 => some [(1,0),(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(5,1),(8,1)]
  | 18 => some [(7,4)]
  | 19 => some [(1,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(8,3)]
  | 25 => some [(8,5)]
  | 26 => some [(8,1)]
  | 27 => some [(6,5)]
  | 28 => some [(0,4)]
  | 29 => some [(5,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(6,3)]
  | 34 => some [(7,2)]
  | 35 => some [(5,5)]
  | 36 => some [(7,0)]
  | 37 => some [(4,3)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(4,1)]
  | 41 => some [(0,2)]
  | 42 => some [(1,1)]
  | 43 => some [(4,4)]
  | 44 => some [(1,4)]
  | 45 => some [(0,5)]
  | 46 => some [(2,0)]
  | 47 => some [(7,3)]
  | 48 => some [(5,2)]
  | 49 => some [(8,0)]
  | 50 => some [(7,5)]
  | 51 => some [(6,0)]
  | 52 => some [(3,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(8,2)]
  | 57 => some [(5,0)]
  | 58 => some [(4,5)]
  | 59 => some [(1,0)]
  | _ => some [(7,1)]
theorem root0Node13Domains4_fast_eq : root0Node13Domains4 = expandDomains root0Node13Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node13Domains4 v = expandDomains root0Node13Domains4Fast v from by decide) v
theorem root0Node13Step4Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root0Node13Domains3 root0Node13Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node13Domains3 root0Node13Domains4
    root0Node13Domains3Fast root0Node13Domains4Fast
    root0Node13Domains3_fast_eq root0Node13Domains4_fast_eq (by decide)
theorem root0Node13Step4_checked :
    checkReplacement table39 root0Node13Domains3 root0Node13Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node13Step4Chunk0_0_checked, root0Node13Step4Chunk0_1_checked, root0Node13Step4Chunk0_2_checked, root0Node13Step4Chunk0_3_checked, root0Node13Step4Chunk0_4_checked, root0Node13Step4Chunk0_5_checked, root0Node13Step4Chunk1_0_checked, root0Node13Step4Chunk1_1_checked, root0Node13Step4Chunk1_2_checked, root0Node13Step4Chunk1_3_checked, root0Node13Step4Chunk1_4_checked, root0Node13Step4Chunk1_5_checked, root0Node13Step4Chunk2_0_checked, root0Node13Step4Chunk2_1_checked, root0Node13Step4Chunk2_2_checked, root0Node13Step4Chunk2_3_checked, root0Node13Step4Chunk2_4_checked, root0Node13Step4Chunk2_5_checked, root0Node13Step4Chunk3_0_checked, root0Node13Step4Chunk3_1_checked, root0Node13Step4Chunk3_2_checked, root0Node13Step4Chunk3_3_checked, root0Node13Step4Chunk3_4_checked, root0Node13Step4Chunk3_5_checked, root0Node13Step4Chunk4_0_checked, root0Node13Step4Chunk4_1_checked, root0Node13Step4Chunk4_2_checked, root0Node13Step4Chunk4_3_checked, root0Node13Step4Chunk4_4_checked, root0Node13Step4Chunk4_5_checked, root0Node13Step4Chunk5_0_checked, root0Node13Step4Chunk5_1_checked, root0Node13Step4Chunk5_2_checked, root0Node13Step4Chunk5_3_checked, root0Node13Step4Chunk5_4_checked, root0Node13Step4Chunk5_5_checked, root0Node13Step4Chunk6_0_checked, root0Node13Step4Chunk6_1_checked, root0Node13Step4Chunk6_2_checked, root0Node13Step4Chunk6_3_checked, root0Node13Step4Chunk6_4_checked, root0Node13Step4Chunk6_5_checked, root0Node13Step4Chunk7_0_checked, root0Node13Step4Chunk7_1_checked, root0Node13Step4Chunk7_2_checked, root0Node13Step4Chunk7_3_checked, root0Node13Step4Chunk7_4_checked, root0Node13Step4Chunk7_5_checked, root0Node13Step4Chunk8_0_checked, root0Node13Step4Chunk8_1_checked, root0Node13Step4Chunk8_2_checked, root0Node13Step4Chunk8_3_checked, root0Node13Step4Chunk8_4_checked, root0Node13Step4Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
