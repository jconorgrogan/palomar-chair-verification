module

public import SpectreFinite.RadiusFourRoot8Part14
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable18
public import SpectreFinite.RadiusFourTable2
public import SpectreFinite.RadiusFourTable21
public import SpectreFinite.RadiusFourTable23
public import SpectreFinite.RadiusFourTable38

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node46Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(1,5),(6,0)]
  | 1 => [(1,1),(6,1),(7,1)]
  | 2 => [(4,1),(7,5),(8,1)]
  | 3 => [(0,2),(6,0),(6,5)]
  | 4 => [(0,4),(1,1),(6,1),(6,2),(7,1)]
  | 5 => [(1,2),(3,2),(5,2),(5,5),(7,2)]
  | 6 => [(4,0),(7,0),(8,0)]
  | 7 => [(7,3),(8,3)]
  | 8 => [(5,2),(5,5),(8,2)]
  | 9 => [(7,0),(8,0)]
  | 10 => [(2,3),(4,3),(7,1),(7,3),(8,3)]
  | 11 => [(0,3),(0,4),(0,5),(6,1),(6,2)]
  | 12 => [(4,4),(5,1),(5,4),(8,4)]
  | 13 => [(0,1),(1,4)]
  | 14 => [(0,5),(6,2)]
  | 15 => [(4,4),(8,4)]
  | 16 => [(1,4),(6,4)]
  | 17 => [(0,5),(1,2)]
  | 18 => [(1,0),(4,2),(6,0),(7,0)]
  | 19 => [(4,3),(5,3),(7,1),(8,3)]
  | 20 => [(7,5),(8,5)]
  | 21 => [(1,0),(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3),(6,0)]
  | 25 => [(3,1),(5,1),(7,1),(8,1)]
  | 26 => [(1,2),(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(1,3),(7,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2),(8,2)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5),(8,5)]
  | 35 => [(5,1),(8,1)]
  | 36 => [(0,1),(6,5)]
  | 37 => [(0,4),(6,2)]
  | 38 => [(5,4),(8,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(7,4),(8,4)]
  | 42 => [(0,0),(1,3),(6,3)]
  | 43 => [(5,5),(8,5)]
  | 44 => [(1,0),(7,0)]
  | 45 => [(4,3),(7,1)]
  | 46 => [(3,5),(7,5)]
  | 47 => [(0,3)]
  | 48 => [(4,1),(8,1)]
  | 49 => [(0,2),(1,5),(6,5)]
  | 50 => [(4,4),(7,2),(8,2)]
  | 51 => [(1,4),(4,0),(7,4),(8,0)]
  | 52 => [(0,5),(1,3),(6,3),(7,3)]
  | 53 => [(2,2),(2,4),(4,2)]
  | 54 => [(1,3),(3,3),(5,3)]
  | 55 => [(5,2),(5,5),(8,5)]
  | 56 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 57 => [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 58 => [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 59 => [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => [(0,4),(0,5),(6,2),(6,3)]
def root8Node46Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0)]
  | 1 => some [(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(7,5),(8,1)]
  | 3 => some [(0,2),(6,0),(6,5)]
  | 4 => some [(0,4),(1,1),(6,1),(6,2),(7,1)]
  | 5 => some [(1,2),(3,2),(5,2),(5,5),(7,2)]
  | 6 => some [(4,0),(7,0),(8,0)]
  | 7 => some [(7,3),(8,3)]
  | 8 => some [(5,2),(5,5),(8,2)]
  | 9 => some [(7,0),(8,0)]
  | 10 => some [(2,3),(4,3),(7,1),(7,3),(8,3)]
  | 11 => some [(0,3),(0,4),(0,5),(6,1),(6,2)]
  | 12 => some [(4,4),(5,1),(5,4),(8,4)]
  | 13 => some [(0,1),(1,4)]
  | 14 => some [(0,5),(6,2)]
  | 15 => some [(4,4),(8,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(1,0),(4,2),(6,0),(7,0)]
  | 19 => some [(4,3),(5,3),(7,1),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(1,0),(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(3,1),(5,1),(7,1),(8,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(8,5)]
  | 35 => some [(5,1),(8,1)]
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(1,3),(6,3)]
  | 43 => some [(5,5),(8,5)]
  | 44 => some [(1,0),(7,0)]
  | 45 => some [(4,3),(7,1)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(4,1),(8,1)]
  | 49 => some [(0,2),(1,5),(6,5)]
  | 50 => some [(4,4),(7,2),(8,2)]
  | 51 => some [(1,4),(4,0),(7,4),(8,0)]
  | 52 => some [(0,5),(1,3),(6,3),(7,3)]
  | 53 => some [(2,2),(2,4),(4,2)]
  | 54 => some [(1,3),(3,3),(5,3)]
  | 55 => some [(5,2),(5,5),(8,5)]
  | 56 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 57 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 58 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 59 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => some [(0,4),(0,5),(6,2),(6,3)]
theorem root8Node46Domains3_fast_eq : root8Node46Domains3 = expandDomains root8Node46Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node46Domains3 v = expandDomains root8Node46Domains3Fast v from by decide) v
theorem root8Node46Step3Chunk0_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_0⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk0_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_1⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk0_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_2⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk0_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_3⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk0_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_4⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk0_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows0_5⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk1_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_0⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk1_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_1⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk1_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_2⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk1_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_3⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk1_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_4⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk1_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows1_5⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk2_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_0⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk2_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_1⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk2_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_2⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk2_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_3⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk2_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_4⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk2_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows2_5⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk3_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_0⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk3_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_1⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk3_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_2⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk3_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_3⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk3_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_4⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk3_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows3_5⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk4_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_0⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk4_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_1⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk4_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_2⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk4_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_3⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk4_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_4⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk4_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows4_5⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk5_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_0⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk5_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_1⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk5_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_2⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk5_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_3⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk5_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_4⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk5_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows5_5⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk6_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_0⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk6_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_1⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk6_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_2⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk6_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_3⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk6_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_4⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk6_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows6_5⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk7_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_0⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk7_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_1⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk7_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_2⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk7_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_3⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk7_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_4⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk7_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows7_5⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk8_0_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_0⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk8_1_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_1⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk8_2_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_2⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk8_3_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_3⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk8_4_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_4⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3Chunk8_5_checked :
    checkNarrowing ⟨table18Scope, table18Rows8_5⟩
      root8Node46Domains2 root8Node46Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains2 root8Node46Domains3
    root8Node46Domains2Fast root8Node46Domains3Fast
    root8Node46Domains2_fast_eq root8Node46Domains3_fast_eq (by decide)
theorem root8Node46Step3_checked :
    checkReplacement table18 root8Node46Domains2 root8Node46Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node46Step3Chunk0_0_checked, root8Node46Step3Chunk0_1_checked, root8Node46Step3Chunk0_2_checked, root8Node46Step3Chunk0_3_checked, root8Node46Step3Chunk0_4_checked, root8Node46Step3Chunk0_5_checked, root8Node46Step3Chunk1_0_checked, root8Node46Step3Chunk1_1_checked, root8Node46Step3Chunk1_2_checked, root8Node46Step3Chunk1_3_checked, root8Node46Step3Chunk1_4_checked, root8Node46Step3Chunk1_5_checked, root8Node46Step3Chunk2_0_checked, root8Node46Step3Chunk2_1_checked, root8Node46Step3Chunk2_2_checked, root8Node46Step3Chunk2_3_checked, root8Node46Step3Chunk2_4_checked, root8Node46Step3Chunk2_5_checked, root8Node46Step3Chunk3_0_checked, root8Node46Step3Chunk3_1_checked, root8Node46Step3Chunk3_2_checked, root8Node46Step3Chunk3_3_checked, root8Node46Step3Chunk3_4_checked, root8Node46Step3Chunk3_5_checked, root8Node46Step3Chunk4_0_checked, root8Node46Step3Chunk4_1_checked, root8Node46Step3Chunk4_2_checked, root8Node46Step3Chunk4_3_checked, root8Node46Step3Chunk4_4_checked, root8Node46Step3Chunk4_5_checked, root8Node46Step3Chunk5_0_checked, root8Node46Step3Chunk5_1_checked, root8Node46Step3Chunk5_2_checked, root8Node46Step3Chunk5_3_checked, root8Node46Step3Chunk5_4_checked, root8Node46Step3Chunk5_5_checked, root8Node46Step3Chunk6_0_checked, root8Node46Step3Chunk6_1_checked, root8Node46Step3Chunk6_2_checked, root8Node46Step3Chunk6_3_checked, root8Node46Step3Chunk6_4_checked, root8Node46Step3Chunk6_5_checked, root8Node46Step3Chunk7_0_checked, root8Node46Step3Chunk7_1_checked, root8Node46Step3Chunk7_2_checked, root8Node46Step3Chunk7_3_checked, root8Node46Step3Chunk7_4_checked, root8Node46Step3Chunk7_5_checked, root8Node46Step3Chunk8_0_checked, root8Node46Step3Chunk8_1_checked, root8Node46Step3Chunk8_2_checked, root8Node46Step3Chunk8_3_checked, root8Node46Step3Chunk8_4_checked, root8Node46Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node46Domains4 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(1,5),(6,0)]
  | 1 => [(1,1),(6,1),(7,1)]
  | 2 => [(4,1),(7,5),(8,1)]
  | 3 => [(0,2),(6,0),(6,5)]
  | 4 => [(0,4),(1,1),(7,1)]
  | 5 => [(1,2),(3,2),(5,2),(5,5),(7,2)]
  | 6 => [(4,0),(7,0),(8,0)]
  | 7 => [(7,3),(8,3)]
  | 8 => [(5,2),(5,5),(8,2)]
  | 9 => [(7,0),(8,0)]
  | 10 => [(2,3),(4,3),(7,3),(8,3)]
  | 11 => [(0,3),(0,4),(0,5),(6,1),(6,2)]
  | 12 => [(4,4),(5,1),(5,4),(8,4)]
  | 13 => [(0,1),(1,4)]
  | 14 => [(0,5),(6,2)]
  | 15 => [(4,4),(8,4)]
  | 16 => [(1,4),(6,4)]
  | 17 => [(0,5),(1,2)]
  | 18 => [(1,0),(4,2),(6,0),(7,0)]
  | 19 => [(4,3),(5,3),(7,1),(8,3)]
  | 20 => [(7,5),(8,5)]
  | 21 => [(1,0),(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3),(6,0)]
  | 25 => [(3,1),(5,1),(7,1),(8,1)]
  | 26 => [(1,2),(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(1,3),(7,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2),(8,2)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5),(8,5)]
  | 35 => [(5,1),(8,1)]
  | 36 => [(0,1),(6,5)]
  | 37 => [(0,4),(6,2)]
  | 38 => [(5,4),(8,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(7,4),(8,4)]
  | 42 => [(0,0),(1,3),(6,3)]
  | 43 => [(5,5),(8,5)]
  | 44 => [(1,0),(7,0)]
  | 45 => [(4,3),(7,1)]
  | 46 => [(3,5),(7,5)]
  | 47 => [(0,3)]
  | 48 => [(4,1),(8,1)]
  | 49 => [(0,2),(1,5),(6,5)]
  | 50 => [(4,4),(7,2),(8,2)]
  | 51 => [(1,4),(4,0),(7,4),(8,0)]
  | 52 => [(0,5),(1,3),(6,3),(7,3)]
  | 53 => [(2,2),(2,4),(4,2)]
  | 54 => [(1,3),(3,3),(5,3)]
  | 55 => [(5,2),(5,5),(8,5)]
  | 56 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 57 => [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 58 => [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 59 => [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => [(0,4),(0,5),(6,2),(6,3)]
def root8Node46Domains4Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0)]
  | 1 => some [(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(7,5),(8,1)]
  | 3 => some [(0,2),(6,0),(6,5)]
  | 4 => some [(0,4),(1,1),(7,1)]
  | 5 => some [(1,2),(3,2),(5,2),(5,5),(7,2)]
  | 6 => some [(4,0),(7,0),(8,0)]
  | 7 => some [(7,3),(8,3)]
  | 8 => some [(5,2),(5,5),(8,2)]
  | 9 => some [(7,0),(8,0)]
  | 10 => some [(2,3),(4,3),(7,3),(8,3)]
  | 11 => some [(0,3),(0,4),(0,5),(6,1),(6,2)]
  | 12 => some [(4,4),(5,1),(5,4),(8,4)]
  | 13 => some [(0,1),(1,4)]
  | 14 => some [(0,5),(6,2)]
  | 15 => some [(4,4),(8,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(1,0),(4,2),(6,0),(7,0)]
  | 19 => some [(4,3),(5,3),(7,1),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(1,0),(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(3,1),(5,1),(7,1),(8,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(8,5)]
  | 35 => some [(5,1),(8,1)]
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(1,3),(6,3)]
  | 43 => some [(5,5),(8,5)]
  | 44 => some [(1,0),(7,0)]
  | 45 => some [(4,3),(7,1)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(4,1),(8,1)]
  | 49 => some [(0,2),(1,5),(6,5)]
  | 50 => some [(4,4),(7,2),(8,2)]
  | 51 => some [(1,4),(4,0),(7,4),(8,0)]
  | 52 => some [(0,5),(1,3),(6,3),(7,3)]
  | 53 => some [(2,2),(2,4),(4,2)]
  | 54 => some [(1,3),(3,3),(5,3)]
  | 55 => some [(5,2),(5,5),(8,5)]
  | 56 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 57 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 58 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 59 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => some [(0,4),(0,5),(6,2),(6,3)]
theorem root8Node46Domains4_fast_eq : root8Node46Domains4 = expandDomains root8Node46Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node46Domains4 v = expandDomains root8Node46Domains4Fast v from by decide) v
theorem root8Node46Step4Chunk0_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_0⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk0_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_1⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk0_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_2⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk0_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_3⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk0_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_4⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk0_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_5⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk1_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_0⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk1_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_1⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk1_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_2⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk1_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_3⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk1_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_4⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk1_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_5⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk2_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_0⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk2_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_1⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk2_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_2⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk2_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_3⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk2_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_4⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk2_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_5⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk3_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_0⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk3_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_1⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk3_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_2⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk3_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_3⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk3_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_4⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk3_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_5⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk4_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_0⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk4_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_1⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk4_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_2⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk4_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_3⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk4_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_4⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk4_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_5⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk5_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_0⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk5_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_1⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk5_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_2⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk5_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_3⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk5_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_4⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk5_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_5⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk6_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_0⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk6_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_1⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk6_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_2⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk6_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_3⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk6_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_4⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk6_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_5⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk7_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_0⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk7_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_1⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk7_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_2⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk7_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_3⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk7_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_4⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk7_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_5⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk8_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_0⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk8_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_1⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk8_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_2⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk8_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_3⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk8_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_4⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4Chunk8_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_5⟩
      root8Node46Domains3 root8Node46Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node46Domains3 root8Node46Domains4
    root8Node46Domains3Fast root8Node46Domains4Fast
    root8Node46Domains3_fast_eq root8Node46Domains4_fast_eq (by decide)
theorem root8Node46Step4_checked :
    checkReplacement table2 root8Node46Domains3 root8Node46Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node46Step4Chunk0_0_checked, root8Node46Step4Chunk0_1_checked, root8Node46Step4Chunk0_2_checked, root8Node46Step4Chunk0_3_checked, root8Node46Step4Chunk0_4_checked, root8Node46Step4Chunk0_5_checked, root8Node46Step4Chunk1_0_checked, root8Node46Step4Chunk1_1_checked, root8Node46Step4Chunk1_2_checked, root8Node46Step4Chunk1_3_checked, root8Node46Step4Chunk1_4_checked, root8Node46Step4Chunk1_5_checked, root8Node46Step4Chunk2_0_checked, root8Node46Step4Chunk2_1_checked, root8Node46Step4Chunk2_2_checked, root8Node46Step4Chunk2_3_checked, root8Node46Step4Chunk2_4_checked, root8Node46Step4Chunk2_5_checked, root8Node46Step4Chunk3_0_checked, root8Node46Step4Chunk3_1_checked, root8Node46Step4Chunk3_2_checked, root8Node46Step4Chunk3_3_checked, root8Node46Step4Chunk3_4_checked, root8Node46Step4Chunk3_5_checked, root8Node46Step4Chunk4_0_checked, root8Node46Step4Chunk4_1_checked, root8Node46Step4Chunk4_2_checked, root8Node46Step4Chunk4_3_checked, root8Node46Step4Chunk4_4_checked, root8Node46Step4Chunk4_5_checked, root8Node46Step4Chunk5_0_checked, root8Node46Step4Chunk5_1_checked, root8Node46Step4Chunk5_2_checked, root8Node46Step4Chunk5_3_checked, root8Node46Step4Chunk5_4_checked, root8Node46Step4Chunk5_5_checked, root8Node46Step4Chunk6_0_checked, root8Node46Step4Chunk6_1_checked, root8Node46Step4Chunk6_2_checked, root8Node46Step4Chunk6_3_checked, root8Node46Step4Chunk6_4_checked, root8Node46Step4Chunk6_5_checked, root8Node46Step4Chunk7_0_checked, root8Node46Step4Chunk7_1_checked, root8Node46Step4Chunk7_2_checked, root8Node46Step4Chunk7_3_checked, root8Node46Step4Chunk7_4_checked, root8Node46Step4Chunk7_5_checked, root8Node46Step4Chunk8_0_checked, root8Node46Step4Chunk8_1_checked, root8Node46Step4Chunk8_2_checked, root8Node46Step4Chunk8_3_checked, root8Node46Step4Chunk8_4_checked, root8Node46Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node47Domains0 : Domains 61 State := restrict root8Node46Domains4 7 (7,3)
def root8Node47Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0)]
  | 1 => some [(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(7,5),(8,1)]
  | 3 => some [(0,2),(6,0),(6,5)]
  | 4 => some [(0,4),(1,1),(7,1)]
  | 5 => some [(1,2),(3,2),(5,2),(5,5),(7,2)]
  | 6 => some [(4,0),(7,0),(8,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2),(5,5),(8,2)]
  | 9 => some [(7,0),(8,0)]
  | 10 => some [(2,3),(4,3),(7,3),(8,3)]
  | 11 => some [(0,3),(0,4),(0,5),(6,1),(6,2)]
  | 12 => some [(4,4),(5,1),(5,4),(8,4)]
  | 13 => some [(0,1),(1,4)]
  | 14 => some [(0,5),(6,2)]
  | 15 => some [(4,4),(8,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(1,0),(4,2),(6,0),(7,0)]
  | 19 => some [(4,3),(5,3),(7,1),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(1,0),(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(3,1),(5,1),(7,1),(8,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(8,5)]
  | 35 => some [(5,1),(8,1)]
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(1,3),(6,3)]
  | 43 => some [(5,5),(8,5)]
  | 44 => some [(1,0),(7,0)]
  | 45 => some [(4,3),(7,1)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(4,1),(8,1)]
  | 49 => some [(0,2),(1,5),(6,5)]
  | 50 => some [(4,4),(7,2),(8,2)]
  | 51 => some [(1,4),(4,0),(7,4),(8,0)]
  | 52 => some [(0,5),(1,3),(6,3),(7,3)]
  | 53 => some [(2,2),(2,4),(4,2)]
  | 54 => some [(1,3),(3,3),(5,3)]
  | 55 => some [(5,2),(5,5),(8,5)]
  | 56 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 57 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 58 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 59 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => some [(0,4),(0,5),(6,2),(6,3)]
theorem root8Node47Domains0_fast_eq : root8Node47Domains0 = expandDomains root8Node47Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node47Domains0 v = expandDomains root8Node47Domains0Fast v from by decide) v
def root8Node47Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(6,0)]
  | 1 => [(1,1),(7,1)]
  | 2 => [(4,1),(7,5)]
  | 3 => [(0,2),(6,0)]
  | 4 => [(0,4),(1,1),(7,1)]
  | 5 => [(1,2),(3,2),(7,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(5,2),(8,2)]
  | 9 => [(8,0)]
  | 10 => [(2,3),(4,3),(7,3),(8,3)]
  | 11 => [(0,3),(6,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(1,4),(6,4)]
  | 17 => [(0,5),(1,2)]
  | 18 => [(4,2),(7,0)]
  | 19 => [(5,3),(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3),(6,0)]
  | 25 => [(3,1),(5,1),(7,1),(8,1)]
  | 26 => [(1,2),(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2),(8,2)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5),(8,5)]
  | 35 => [(5,1),(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(7,4),(8,4)]
  | 42 => [(0,0),(1,3),(6,3)]
  | 43 => [(5,5),(8,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(3,5),(7,5)]
  | 47 => [(0,3)]
  | 48 => [(4,1),(8,1)]
  | 49 => [(0,2),(1,5),(6,5)]
  | 50 => [(4,4),(7,2),(8,2)]
  | 51 => [(1,4),(4,0),(7,4),(8,0)]
  | 52 => [(0,5),(1,3),(6,3),(7,3)]
  | 53 => [(2,2),(2,4),(4,2)]
  | 54 => [(1,3),(3,3),(5,3)]
  | 55 => [(5,2),(5,5),(8,5)]
  | 56 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 57 => [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 58 => [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 59 => [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => [(0,4),(0,5),(6,2),(6,3)]
def root8Node47Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(6,0)]
  | 1 => some [(1,1),(7,1)]
  | 2 => some [(4,1),(7,5)]
  | 3 => some [(0,2),(6,0)]
  | 4 => some [(0,4),(1,1),(7,1)]
  | 5 => some [(1,2),(3,2),(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2),(8,2)]
  | 9 => some [(8,0)]
  | 10 => some [(2,3),(4,3),(7,3),(8,3)]
  | 11 => some [(0,3),(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(4,2),(7,0)]
  | 19 => some [(5,3),(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(3,1),(5,1),(7,1),(8,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(8,5)]
  | 35 => some [(5,1),(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(1,3),(6,3)]
  | 43 => some [(5,5),(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(4,1),(8,1)]
  | 49 => some [(0,2),(1,5),(6,5)]
  | 50 => some [(4,4),(7,2),(8,2)]
  | 51 => some [(1,4),(4,0),(7,4),(8,0)]
  | 52 => some [(0,5),(1,3),(6,3),(7,3)]
  | 53 => some [(2,2),(2,4),(4,2)]
  | 54 => some [(1,3),(3,3),(5,3)]
  | 55 => some [(5,2),(5,5),(8,5)]
  | 56 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 57 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 58 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 59 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | _ => some [(0,4),(0,5),(6,2),(6,3)]
theorem root8Node47Domains1_fast_eq : root8Node47Domains1 = expandDomains root8Node47Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node47Domains1 v = expandDomains root8Node47Domains1Fast v from by decide) v
theorem root8Node47Step1Chunk0_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_0⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk0_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_1⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk0_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_2⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk0_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_3⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk0_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_4⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk0_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_5⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk1_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_0⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk1_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_1⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk1_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_2⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk1_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_3⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk1_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_4⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk1_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_5⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk2_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_0⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk2_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_1⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk2_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_2⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk2_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_3⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk2_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_4⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk2_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_5⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk3_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_0⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk3_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_1⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk3_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_2⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk3_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_3⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk3_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_4⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk3_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_5⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk4_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_0⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk4_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_1⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk4_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_2⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk4_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_3⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk4_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_4⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk4_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_5⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk5_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_0⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk5_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_1⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk5_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_2⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk5_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_3⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk5_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_4⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk5_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_5⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk6_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_0⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk6_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_1⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk6_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_2⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk6_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_3⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk6_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_4⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk6_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_5⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk7_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_0⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk7_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_1⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk7_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_2⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk7_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_3⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk7_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_4⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk7_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_5⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk8_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_0⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk8_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_1⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk8_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_2⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk8_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_3⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk8_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_4⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1Chunk8_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_5⟩
      root8Node47Domains0 root8Node47Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains0 root8Node47Domains1
    root8Node47Domains0Fast root8Node47Domains1Fast
    root8Node47Domains0_fast_eq root8Node47Domains1_fast_eq (by decide)
theorem root8Node47Step1_checked :
    checkReplacement table21 root8Node47Domains0 root8Node47Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node47Step1Chunk0_0_checked, root8Node47Step1Chunk0_1_checked, root8Node47Step1Chunk0_2_checked, root8Node47Step1Chunk0_3_checked, root8Node47Step1Chunk0_4_checked, root8Node47Step1Chunk0_5_checked, root8Node47Step1Chunk1_0_checked, root8Node47Step1Chunk1_1_checked, root8Node47Step1Chunk1_2_checked, root8Node47Step1Chunk1_3_checked, root8Node47Step1Chunk1_4_checked, root8Node47Step1Chunk1_5_checked, root8Node47Step1Chunk2_0_checked, root8Node47Step1Chunk2_1_checked, root8Node47Step1Chunk2_2_checked, root8Node47Step1Chunk2_3_checked, root8Node47Step1Chunk2_4_checked, root8Node47Step1Chunk2_5_checked, root8Node47Step1Chunk3_0_checked, root8Node47Step1Chunk3_1_checked, root8Node47Step1Chunk3_2_checked, root8Node47Step1Chunk3_3_checked, root8Node47Step1Chunk3_4_checked, root8Node47Step1Chunk3_5_checked, root8Node47Step1Chunk4_0_checked, root8Node47Step1Chunk4_1_checked, root8Node47Step1Chunk4_2_checked, root8Node47Step1Chunk4_3_checked, root8Node47Step1Chunk4_4_checked, root8Node47Step1Chunk4_5_checked, root8Node47Step1Chunk5_0_checked, root8Node47Step1Chunk5_1_checked, root8Node47Step1Chunk5_2_checked, root8Node47Step1Chunk5_3_checked, root8Node47Step1Chunk5_4_checked, root8Node47Step1Chunk5_5_checked, root8Node47Step1Chunk6_0_checked, root8Node47Step1Chunk6_1_checked, root8Node47Step1Chunk6_2_checked, root8Node47Step1Chunk6_3_checked, root8Node47Step1Chunk6_4_checked, root8Node47Step1Chunk6_5_checked, root8Node47Step1Chunk7_0_checked, root8Node47Step1Chunk7_1_checked, root8Node47Step1Chunk7_2_checked, root8Node47Step1Chunk7_3_checked, root8Node47Step1Chunk7_4_checked, root8Node47Step1Chunk7_5_checked, root8Node47Step1Chunk8_0_checked, root8Node47Step1Chunk8_1_checked, root8Node47Step1Chunk8_2_checked, root8Node47Step1Chunk8_3_checked, root8Node47Step1Chunk8_4_checked, root8Node47Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node47Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(6,0)]
  | 1 => [(1,1),(7,1)]
  | 2 => [(4,1),(7,5)]
  | 3 => [(0,2),(6,0)]
  | 4 => [(0,4),(1,1),(7,1)]
  | 5 => [(1,2),(3,2),(7,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(5,2),(8,2)]
  | 9 => [(8,0)]
  | 10 => [(2,3),(4,3),(7,3),(8,3)]
  | 11 => [(0,3),(6,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(1,4),(6,4)]
  | 17 => [(0,5),(1,2)]
  | 18 => [(4,2),(7,0)]
  | 19 => [(5,3),(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3),(6,0)]
  | 25 => [(3,1),(5,1),(7,1),(8,1)]
  | 26 => [(1,2),(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2),(8,2)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5),(8,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(7,4),(8,4)]
  | 42 => [(0,0),(1,3),(6,3)]
  | 43 => [(5,5),(8,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(3,5),(7,5)]
  | 47 => [(0,3)]
  | 48 => [(4,1),(8,1)]
  | 49 => [(0,2),(1,5),(6,5)]
  | 50 => [(4,4),(7,2)]
  | 51 => [(1,4),(7,4)]
  | 52 => [(0,5),(1,3),(6,3)]
  | 53 => [(2,2),(2,4),(4,2)]
  | 54 => [(1,3),(3,3),(5,3)]
  | 55 => [(5,2),(5,5),(8,5)]
  | 56 => [(4,1),(7,5),(8,1)]
  | 57 => [(0,2),(6,0),(6,5)]
  | 58 => [(0,4),(1,1),(7,1)]
  | 59 => [(0,1),(1,4),(3,4),(6,5)]
  | _ => [(0,4),(0,5),(6,2),(6,3)]
def root8Node47Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(6,0)]
  | 1 => some [(1,1),(7,1)]
  | 2 => some [(4,1),(7,5)]
  | 3 => some [(0,2),(6,0)]
  | 4 => some [(0,4),(1,1),(7,1)]
  | 5 => some [(1,2),(3,2),(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2),(8,2)]
  | 9 => some [(8,0)]
  | 10 => some [(2,3),(4,3),(7,3),(8,3)]
  | 11 => some [(0,3),(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(4,2),(7,0)]
  | 19 => some [(5,3),(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(3,1),(5,1),(7,1),(8,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(1,3),(6,3)]
  | 43 => some [(5,5),(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(4,1),(8,1)]
  | 49 => some [(0,2),(1,5),(6,5)]
  | 50 => some [(4,4),(7,2)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(1,3),(6,3)]
  | 53 => some [(2,2),(2,4),(4,2)]
  | 54 => some [(1,3),(3,3),(5,3)]
  | 55 => some [(5,2),(5,5),(8,5)]
  | 56 => some [(4,1),(7,5),(8,1)]
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(0,4),(1,1),(7,1)]
  | 59 => some [(0,1),(1,4),(3,4),(6,5)]
  | _ => some [(0,4),(0,5),(6,2),(6,3)]
theorem root8Node47Domains2_fast_eq : root8Node47Domains2 = expandDomains root8Node47Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node47Domains2 v = expandDomains root8Node47Domains2Fast v from by decide) v
theorem root8Node47Step2Chunk0_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_0⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk0_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_1⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk0_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_2⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk0_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_3⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk0_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_4⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk0_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_5⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk1_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_0⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk1_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_1⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk1_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_2⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk1_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_3⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk1_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_4⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk1_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_5⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk2_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_0⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk2_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_1⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk2_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_2⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk2_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_3⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk2_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_4⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk2_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_5⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk3_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_0⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk3_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_1⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk3_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_2⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk3_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_3⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk3_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_4⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk3_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_5⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk4_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_0⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk4_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_1⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk4_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_2⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk4_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_3⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk4_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_4⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk4_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_5⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk5_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_0⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk5_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_1⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk5_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_2⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk5_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_3⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk5_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_4⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk5_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_5⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk6_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_0⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk6_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_1⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk6_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_2⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk6_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_3⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk6_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_4⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk6_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_5⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk7_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_0⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk7_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_1⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk7_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_2⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk7_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_3⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk7_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_4⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk7_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_5⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk8_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_0⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk8_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_1⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk8_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_2⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk8_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_3⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk8_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_4⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2Chunk8_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_5⟩
      root8Node47Domains1 root8Node47Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains1 root8Node47Domains2
    root8Node47Domains1Fast root8Node47Domains2Fast
    root8Node47Domains1_fast_eq root8Node47Domains2_fast_eq (by decide)
theorem root8Node47Step2_checked :
    checkReplacement table38 root8Node47Domains1 root8Node47Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node47Step2Chunk0_0_checked, root8Node47Step2Chunk0_1_checked, root8Node47Step2Chunk0_2_checked, root8Node47Step2Chunk0_3_checked, root8Node47Step2Chunk0_4_checked, root8Node47Step2Chunk0_5_checked, root8Node47Step2Chunk1_0_checked, root8Node47Step2Chunk1_1_checked, root8Node47Step2Chunk1_2_checked, root8Node47Step2Chunk1_3_checked, root8Node47Step2Chunk1_4_checked, root8Node47Step2Chunk1_5_checked, root8Node47Step2Chunk2_0_checked, root8Node47Step2Chunk2_1_checked, root8Node47Step2Chunk2_2_checked, root8Node47Step2Chunk2_3_checked, root8Node47Step2Chunk2_4_checked, root8Node47Step2Chunk2_5_checked, root8Node47Step2Chunk3_0_checked, root8Node47Step2Chunk3_1_checked, root8Node47Step2Chunk3_2_checked, root8Node47Step2Chunk3_3_checked, root8Node47Step2Chunk3_4_checked, root8Node47Step2Chunk3_5_checked, root8Node47Step2Chunk4_0_checked, root8Node47Step2Chunk4_1_checked, root8Node47Step2Chunk4_2_checked, root8Node47Step2Chunk4_3_checked, root8Node47Step2Chunk4_4_checked, root8Node47Step2Chunk4_5_checked, root8Node47Step2Chunk5_0_checked, root8Node47Step2Chunk5_1_checked, root8Node47Step2Chunk5_2_checked, root8Node47Step2Chunk5_3_checked, root8Node47Step2Chunk5_4_checked, root8Node47Step2Chunk5_5_checked, root8Node47Step2Chunk6_0_checked, root8Node47Step2Chunk6_1_checked, root8Node47Step2Chunk6_2_checked, root8Node47Step2Chunk6_3_checked, root8Node47Step2Chunk6_4_checked, root8Node47Step2Chunk6_5_checked, root8Node47Step2Chunk7_0_checked, root8Node47Step2Chunk7_1_checked, root8Node47Step2Chunk7_2_checked, root8Node47Step2Chunk7_3_checked, root8Node47Step2Chunk7_4_checked, root8Node47Step2Chunk7_5_checked, root8Node47Step2Chunk8_0_checked, root8Node47Step2Chunk8_1_checked, root8Node47Step2Chunk8_2_checked, root8Node47Step2Chunk8_3_checked, root8Node47Step2Chunk8_4_checked, root8Node47Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node47Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(6,0)]
  | 1 => [(1,1),(7,1)]
  | 2 => [(4,1),(7,5)]
  | 3 => [(0,2),(6,0)]
  | 4 => [(1,1),(7,1)]
  | 5 => [(1,2),(3,2),(7,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(5,2),(8,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3),(8,3)]
  | 11 => [(0,3),(6,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(1,4),(6,4)]
  | 17 => [(0,5),(1,2)]
  | 18 => [(4,2),(7,0)]
  | 19 => [(5,3),(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3),(6,0)]
  | 25 => [(7,1),(8,1)]
  | 26 => [(1,2),(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2),(8,2)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5),(8,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(7,4),(8,4)]
  | 42 => [(0,0),(6,3)]
  | 43 => [(5,5),(8,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(3,5),(7,5)]
  | 47 => [(0,3)]
  | 48 => [(4,1),(8,1)]
  | 49 => [(0,2),(1,5)]
  | 50 => [(4,4),(7,2)]
  | 51 => [(1,4),(7,4)]
  | 52 => [(0,5),(1,3),(6,3)]
  | 53 => [(2,2),(2,4),(4,2)]
  | 54 => [(1,3),(3,3),(5,3)]
  | 55 => [(5,2),(5,5),(8,5)]
  | 56 => [(4,1),(7,5),(8,1)]
  | 57 => [(0,2),(6,0),(6,5)]
  | 58 => [(0,4),(1,1),(7,1)]
  | 59 => [(0,1),(1,4),(3,4),(6,5)]
  | _ => [(0,4),(0,5),(6,2),(6,3)]
def root8Node47Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(6,0)]
  | 1 => some [(1,1),(7,1)]
  | 2 => some [(4,1),(7,5)]
  | 3 => some [(0,2),(6,0)]
  | 4 => some [(1,1),(7,1)]
  | 5 => some [(1,2),(3,2),(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2),(8,2)]
  | 9 => some [(8,0)]
  | 10 => some [(7,3),(8,3)]
  | 11 => some [(0,3),(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(4,2),(7,0)]
  | 19 => some [(5,3),(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(7,1),(8,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(6,3)]
  | 43 => some [(5,5),(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(4,1),(8,1)]
  | 49 => some [(0,2),(1,5)]
  | 50 => some [(4,4),(7,2)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(1,3),(6,3)]
  | 53 => some [(2,2),(2,4),(4,2)]
  | 54 => some [(1,3),(3,3),(5,3)]
  | 55 => some [(5,2),(5,5),(8,5)]
  | 56 => some [(4,1),(7,5),(8,1)]
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(0,4),(1,1),(7,1)]
  | 59 => some [(0,1),(1,4),(3,4),(6,5)]
  | _ => some [(0,4),(0,5),(6,2),(6,3)]
theorem root8Node47Domains3_fast_eq : root8Node47Domains3 = expandDomains root8Node47Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node47Domains3 v = expandDomains root8Node47Domains3Fast v from by decide) v
theorem root8Node47Step3Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root8Node47Domains2 root8Node47Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node47Domains2 root8Node47Domains3
    root8Node47Domains2Fast root8Node47Domains3Fast
    root8Node47Domains2_fast_eq root8Node47Domains3_fast_eq (by decide)
theorem root8Node47Step3_checked :
    checkReplacement table23 root8Node47Domains2 root8Node47Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node47Step3Chunk0_0_checked, root8Node47Step3Chunk0_1_checked, root8Node47Step3Chunk0_2_checked, root8Node47Step3Chunk0_3_checked, root8Node47Step3Chunk0_4_checked, root8Node47Step3Chunk0_5_checked, root8Node47Step3Chunk1_0_checked, root8Node47Step3Chunk1_1_checked, root8Node47Step3Chunk1_2_checked, root8Node47Step3Chunk1_3_checked, root8Node47Step3Chunk1_4_checked, root8Node47Step3Chunk1_5_checked, root8Node47Step3Chunk2_0_checked, root8Node47Step3Chunk2_1_checked, root8Node47Step3Chunk2_2_checked, root8Node47Step3Chunk2_3_checked, root8Node47Step3Chunk2_4_checked, root8Node47Step3Chunk2_5_checked, root8Node47Step3Chunk3_0_checked, root8Node47Step3Chunk3_1_checked, root8Node47Step3Chunk3_2_checked, root8Node47Step3Chunk3_3_checked, root8Node47Step3Chunk3_4_checked, root8Node47Step3Chunk3_5_checked, root8Node47Step3Chunk4_0_checked, root8Node47Step3Chunk4_1_checked, root8Node47Step3Chunk4_2_checked, root8Node47Step3Chunk4_3_checked, root8Node47Step3Chunk4_4_checked, root8Node47Step3Chunk4_5_checked, root8Node47Step3Chunk5_0_checked, root8Node47Step3Chunk5_1_checked, root8Node47Step3Chunk5_2_checked, root8Node47Step3Chunk5_3_checked, root8Node47Step3Chunk5_4_checked, root8Node47Step3Chunk5_5_checked, root8Node47Step3Chunk6_0_checked, root8Node47Step3Chunk6_1_checked, root8Node47Step3Chunk6_2_checked, root8Node47Step3Chunk6_3_checked, root8Node47Step3Chunk6_4_checked, root8Node47Step3Chunk6_5_checked, root8Node47Step3Chunk7_0_checked, root8Node47Step3Chunk7_1_checked, root8Node47Step3Chunk7_2_checked, root8Node47Step3Chunk7_3_checked, root8Node47Step3Chunk7_4_checked, root8Node47Step3Chunk7_5_checked, root8Node47Step3Chunk8_0_checked, root8Node47Step3Chunk8_1_checked, root8Node47Step3Chunk8_2_checked, root8Node47Step3Chunk8_3_checked, root8Node47Step3Chunk8_4_checked, root8Node47Step3Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
