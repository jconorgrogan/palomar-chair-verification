module

public import SpectreFinite.RadiusFiveRoot8Part43
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable12
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node116Domains0 : Domains 91 State := restrict root8Node115Domains3 13 (1,3)
def root8Node116Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(1,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5),(3,5)]
  | 21 => some [(0,1),(6,5)]
  | 22 => some [(0,4),(6,2)]
  | 23 => some [(5,4),(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(2,0),(2,4)]
  | 30 => some [(4,5)]
  | 31 => some [(1,0),(7,0)]
  | 32 => some [(4,3),(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1),(7,1)]
  | 39 => some [(0,1),(6,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0),(7,4)]
  | 43 => some [(1,3),(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1),(8,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(1,3),(6,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(7,4),(8,0)]
  | 73 => some [(1,3),(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(1,1)]
  | 79 => some [(5,1),(5,4),(8,1)]
  | 80 => some [(0,1),(6,4),(6,5)]
  | 81 => some [(0,4),(1,2),(6,2)]
  | 82 => some [(1,4),(3,4),(7,4)]
  | 83 => some [(0,5),(6,3)]
  | 84 => some [(4,4),(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5)]
  | 87 => some [(0,3),(1,0),(3,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5),(4,1)]
  | 89 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root8Node116Domains0_fast_eq : root8Node116Domains0 = expandDomains root8Node116Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node116Domains0 v = expandDomains root8Node116Domains0Fast v from by decide) v
def root8Node116Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(8,2)]
  | 6 => [(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(1,3)]
  | 14 => [(5,2)]
  | 15 => [(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(1,5),(3,5)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(2,0),(2,4)]
  | 30 => [(4,5)]
  | 31 => [(7,0)]
  | 32 => [(4,3)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(3,1),(7,1)]
  | 39 => [(0,1),(6,5)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(1,0),(7,0)]
  | 51 => [(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(8,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(8,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(6,3)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(4,2)]
  | 75 => [(5,3)]
  | 76 => [(5,5),(8,5)]
  | 77 => [(7,0)]
  | 78 => [(1,1)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(1,4),(3,4)]
  | 83 => [(0,5),(6,3)]
  | 84 => [(4,4),(7,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5)]
  | 87 => [(3,0),(7,0)]
  | 88 => [(2,3),(2,5)]
  | 89 => [(0,2),(6,0)]
  | _ => [(1,1),(7,1)]
def root8Node116Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(1,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5),(3,5)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(2,0),(2,4)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(4,3)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1),(7,1)]
  | 39 => some [(0,1),(6,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(1,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(1,4),(3,4)]
  | 83 => some [(0,5),(6,3)]
  | 84 => some [(4,4),(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(3,0),(7,0)]
  | 88 => some [(2,3),(2,5)]
  | 89 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root8Node116Domains1_fast_eq : root8Node116Domains1 = expandDomains root8Node116Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node116Domains1 v = expandDomains root8Node116Domains1Fast v from by decide) v
theorem root8Node116Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq (by decide)
theorem root8Node116Step1Narrowing_checked :
    checkNarrowing table54 root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root8Node116Domains0 root8Node116Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node116Step1Chunk0_0_checked, root8Node116Step1Chunk0_1_checked, root8Node116Step1Chunk0_2_checked, root8Node116Step1Chunk0_3_checked, root8Node116Step1Chunk0_4_checked, root8Node116Step1Chunk0_5_checked, root8Node116Step1Chunk1_0_checked, root8Node116Step1Chunk1_1_checked, root8Node116Step1Chunk1_2_checked, root8Node116Step1Chunk1_3_checked, root8Node116Step1Chunk1_4_checked, root8Node116Step1Chunk1_5_checked, root8Node116Step1Chunk2_0_checked, root8Node116Step1Chunk2_1_checked, root8Node116Step1Chunk2_2_checked, root8Node116Step1Chunk2_3_checked, root8Node116Step1Chunk2_4_checked, root8Node116Step1Chunk2_5_checked, root8Node116Step1Chunk3_0_checked, root8Node116Step1Chunk3_1_checked, root8Node116Step1Chunk3_2_checked, root8Node116Step1Chunk3_3_checked, root8Node116Step1Chunk3_4_checked, root8Node116Step1Chunk3_5_checked, root8Node116Step1Chunk4_0_checked, root8Node116Step1Chunk4_1_checked, root8Node116Step1Chunk4_2_checked, root8Node116Step1Chunk4_3_checked, root8Node116Step1Chunk4_4_checked, root8Node116Step1Chunk4_5_checked, root8Node116Step1Chunk5_0_checked, root8Node116Step1Chunk5_1_checked, root8Node116Step1Chunk5_2_checked, root8Node116Step1Chunk5_3_checked, root8Node116Step1Chunk5_4_checked, root8Node116Step1Chunk5_5_checked, root8Node116Step1Chunk6_0_checked, root8Node116Step1Chunk6_1_checked, root8Node116Step1Chunk6_2_checked, root8Node116Step1Chunk6_3_checked, root8Node116Step1Chunk6_4_checked, root8Node116Step1Chunk6_5_checked, root8Node116Step1Chunk7_0_checked, root8Node116Step1Chunk7_1_checked, root8Node116Step1Chunk7_2_checked, root8Node116Step1Chunk7_3_checked, root8Node116Step1Chunk7_4_checked, root8Node116Step1Chunk7_5_checked, root8Node116Step1Chunk8_0_checked, root8Node116Step1Chunk8_1_checked, root8Node116Step1Chunk8_2_checked, root8Node116Step1Chunk8_3_checked, root8Node116Step1Chunk8_4_checked, root8Node116Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node116Step1_checked :
    checkReplacement table54 root8Node116Domains0 root8Node116Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node116Domains0 root8Node116Domains1
    root8Node116Domains0Fast root8Node116Domains1Fast
    root8Node116Domains0_fast_eq root8Node116Domains1_fast_eq
    root8Node116Step1Narrowing_checked (by decide)
def root8Node117Domains0 : Domains 91 State := restrict root8Node116Domains1 20 (1,5)
def root8Node117Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(1,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(2,0),(2,4)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(4,3)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1),(7,1)]
  | 39 => some [(0,1),(6,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(1,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(1,4),(3,4)]
  | 83 => some [(0,5),(6,3)]
  | 84 => some [(4,4),(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(3,0),(7,0)]
  | 88 => some [(2,3),(2,5)]
  | 89 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root8Node117Domains0_fast_eq : root8Node117Domains0 = expandDomains root8Node117Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node117Domains0 v = expandDomains root8Node117Domains0Fast v from by decide) v
def root8Node117Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(8,2)]
  | 6 => [(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(1,3)]
  | 14 => [(5,2)]
  | 15 => [(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(1,5)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(2,0)]
  | 30 => [(4,5)]
  | 31 => [(7,0)]
  | 32 => [(4,3)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(3,1)]
  | 39 => [(0,1)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(1,0)]
  | 51 => [(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(8,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(8,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(6,3)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(4,2)]
  | 75 => [(5,3)]
  | 76 => [(5,5),(8,5)]
  | 77 => [(7,0)]
  | 78 => [(1,1)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(1,4),(3,4)]
  | 83 => [(0,5),(6,3)]
  | 84 => [(4,4),(7,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5)]
  | 87 => [(3,0),(7,0)]
  | 88 => [(2,3),(2,5)]
  | 89 => [(0,2),(6,0)]
  | _ => [(1,1),(7,1)]
def root8Node117Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(1,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(2,0)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(4,3)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(1,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(1,4),(3,4)]
  | 83 => some [(0,5),(6,3)]
  | 84 => some [(4,4),(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(3,0),(7,0)]
  | 88 => some [(2,3),(2,5)]
  | 89 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root8Node117Domains1_fast_eq : root8Node117Domains1 = expandDomains root8Node117Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node117Domains1 v = expandDomains root8Node117Domains1Fast v from by decide) v
theorem root8Node117Step1Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq (by decide)
theorem root8Node117Step1Narrowing_checked :
    checkNarrowing table12 root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkNarrowing_flatten table12Scope [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5]
    root8Node117Domains0 root8Node117Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node117Step1Chunk0_0_checked, root8Node117Step1Chunk0_1_checked, root8Node117Step1Chunk0_2_checked, root8Node117Step1Chunk0_3_checked, root8Node117Step1Chunk0_4_checked, root8Node117Step1Chunk0_5_checked, root8Node117Step1Chunk1_0_checked, root8Node117Step1Chunk1_1_checked, root8Node117Step1Chunk1_2_checked, root8Node117Step1Chunk1_3_checked, root8Node117Step1Chunk1_4_checked, root8Node117Step1Chunk1_5_checked, root8Node117Step1Chunk2_0_checked, root8Node117Step1Chunk2_1_checked, root8Node117Step1Chunk2_2_checked, root8Node117Step1Chunk2_3_checked, root8Node117Step1Chunk2_4_checked, root8Node117Step1Chunk2_5_checked, root8Node117Step1Chunk3_0_checked, root8Node117Step1Chunk3_1_checked, root8Node117Step1Chunk3_2_checked, root8Node117Step1Chunk3_3_checked, root8Node117Step1Chunk3_4_checked, root8Node117Step1Chunk3_5_checked, root8Node117Step1Chunk4_0_checked, root8Node117Step1Chunk4_1_checked, root8Node117Step1Chunk4_2_checked, root8Node117Step1Chunk4_3_checked, root8Node117Step1Chunk4_4_checked, root8Node117Step1Chunk4_5_checked, root8Node117Step1Chunk5_0_checked, root8Node117Step1Chunk5_1_checked, root8Node117Step1Chunk5_2_checked, root8Node117Step1Chunk5_3_checked, root8Node117Step1Chunk5_4_checked, root8Node117Step1Chunk5_5_checked, root8Node117Step1Chunk6_0_checked, root8Node117Step1Chunk6_1_checked, root8Node117Step1Chunk6_2_checked, root8Node117Step1Chunk6_3_checked, root8Node117Step1Chunk6_4_checked, root8Node117Step1Chunk6_5_checked, root8Node117Step1Chunk7_0_checked, root8Node117Step1Chunk7_1_checked, root8Node117Step1Chunk7_2_checked, root8Node117Step1Chunk7_3_checked, root8Node117Step1Chunk7_4_checked, root8Node117Step1Chunk7_5_checked, root8Node117Step1Chunk8_0_checked, root8Node117Step1Chunk8_1_checked, root8Node117Step1Chunk8_2_checked, root8Node117Step1Chunk8_3_checked, root8Node117Step1Chunk8_4_checked, root8Node117Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node117Step1_checked :
    checkReplacement table12 root8Node117Domains0 root8Node117Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node117Domains0 root8Node117Domains1
    root8Node117Domains0Fast root8Node117Domains1Fast
    root8Node117Domains0_fast_eq root8Node117Domains1_fast_eq
    root8Node117Step1Narrowing_checked (by decide)
def root8Node118Domains0 : Domains 91 State := restrict root8Node117Domains1 76 (5,5)
def root8Node118Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(1,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(2,0)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(4,3)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(5,5)]
  | 77 => some [(7,0)]
  | 78 => some [(1,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(1,4),(3,4)]
  | 83 => some [(0,5),(6,3)]
  | 84 => some [(4,4),(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(3,0),(7,0)]
  | 88 => some [(2,3),(2,5)]
  | 89 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root8Node118Domains0_fast_eq : root8Node118Domains0 = expandDomains root8Node118Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node118Domains0 v = expandDomains root8Node118Domains0Fast v from by decide) v
def root8Node118Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(8,2)]
  | 6 => [(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(1,3)]
  | 14 => [(5,2)]
  | 15 => [(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(1,5)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(2,0)]
  | 30 => [(4,5)]
  | 31 => [(7,0)]
  | 32 => [(4,3)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(3,1)]
  | 39 => [(0,1)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(1,0)]
  | 51 => [(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(8,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(8,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(6,3)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(4,2)]
  | 75 => [(5,3)]
  | 76 => [(5,5)]
  | 77 => [(7,0)]
  | 78 => [(1,1)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(1,4)]
  | 83 => [(0,5)]
  | 84 => [(4,4)]
  | 85 => [(8,3)]
  | 86 => [(5,5)]
  | 87 => [(3,0)]
  | 88 => [(2,5)]
  | 89 => [(6,0)]
  | _ => [(7,1)]
def root8Node118Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(1,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(2,0)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(4,3)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(5,5)]
  | 77 => some [(7,0)]
  | 78 => some [(1,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(1,4)]
  | 83 => some [(0,5)]
  | 84 => some [(4,4)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(3,0)]
  | 88 => some [(2,5)]
  | 89 => some [(6,0)]
  | _ => some [(7,1)]
theorem root8Node118Domains1_fast_eq : root8Node118Domains1 = expandDomains root8Node118Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node118Domains1 v = expandDomains root8Node118Domains1Fast v from by decide) v
theorem root8Node118Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq (by decide)
theorem root8Node118Step1Narrowing_checked :
    checkNarrowing table56 root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root8Node118Domains0 root8Node118Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node118Step1Chunk0_0_checked, root8Node118Step1Chunk0_1_checked, root8Node118Step1Chunk0_2_checked, root8Node118Step1Chunk0_3_checked, root8Node118Step1Chunk0_4_checked, root8Node118Step1Chunk0_5_checked, root8Node118Step1Chunk1_0_checked, root8Node118Step1Chunk1_1_checked, root8Node118Step1Chunk1_2_checked, root8Node118Step1Chunk1_3_checked, root8Node118Step1Chunk1_4_checked, root8Node118Step1Chunk1_5_checked, root8Node118Step1Chunk2_0_checked, root8Node118Step1Chunk2_1_checked, root8Node118Step1Chunk2_2_checked, root8Node118Step1Chunk2_3_checked, root8Node118Step1Chunk2_4_checked, root8Node118Step1Chunk2_5_checked, root8Node118Step1Chunk3_0_checked, root8Node118Step1Chunk3_1_checked, root8Node118Step1Chunk3_2_checked, root8Node118Step1Chunk3_3_checked, root8Node118Step1Chunk3_4_checked, root8Node118Step1Chunk3_5_checked, root8Node118Step1Chunk4_0_checked, root8Node118Step1Chunk4_1_checked, root8Node118Step1Chunk4_2_checked, root8Node118Step1Chunk4_3_checked, root8Node118Step1Chunk4_4_checked, root8Node118Step1Chunk4_5_checked, root8Node118Step1Chunk5_0_checked, root8Node118Step1Chunk5_1_checked, root8Node118Step1Chunk5_2_checked, root8Node118Step1Chunk5_3_checked, root8Node118Step1Chunk5_4_checked, root8Node118Step1Chunk5_5_checked, root8Node118Step1Chunk6_0_checked, root8Node118Step1Chunk6_1_checked, root8Node118Step1Chunk6_2_checked, root8Node118Step1Chunk6_3_checked, root8Node118Step1Chunk6_4_checked, root8Node118Step1Chunk6_5_checked, root8Node118Step1Chunk7_0_checked, root8Node118Step1Chunk7_1_checked, root8Node118Step1Chunk7_2_checked, root8Node118Step1Chunk7_3_checked, root8Node118Step1Chunk7_4_checked, root8Node118Step1Chunk7_5_checked, root8Node118Step1Chunk8_0_checked, root8Node118Step1Chunk8_1_checked, root8Node118Step1Chunk8_2_checked, root8Node118Step1Chunk8_3_checked, root8Node118Step1Chunk8_4_checked, root8Node118Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node118Step1_checked :
    checkReplacement table56 root8Node118Domains0 root8Node118Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node118Domains0 root8Node118Domains1
    root8Node118Domains0Fast root8Node118Domains1Fast
    root8Node118Domains0_fast_eq root8Node118Domains1_fast_eq
    root8Node118Step1Narrowing_checked (by decide)
theorem root8Node118Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node118Domains1 (.output 57) = true := by decide
def root8Node119Domains0 : Domains 91 State := restrict root8Node117Domains1 76 (8,5)
def root8Node119Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(1,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(2,0)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(4,3)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(1,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(1,4),(3,4)]
  | 83 => some [(0,5),(6,3)]
  | 84 => some [(4,4),(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(3,0),(7,0)]
  | 88 => some [(2,3),(2,5)]
  | 89 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root8Node119Domains0_fast_eq : root8Node119Domains0 = expandDomains root8Node119Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node119Domains0 v = expandDomains root8Node119Domains0Fast v from by decide) v
def root8Node119Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(8,2)]
  | 6 => [(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(1,3)]
  | 14 => [(5,2)]
  | 15 => [(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(1,5)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(2,0)]
  | 30 => [(4,5)]
  | 31 => [(7,0)]
  | 32 => [(4,3)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(3,1)]
  | 39 => [(0,1)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(1,0)]
  | 51 => [(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(8,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(8,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(6,3)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(4,2)]
  | 75 => [(5,3)]
  | 76 => [(8,5)]
  | 77 => [(7,0)]
  | 78 => [(1,1)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(3,4)]
  | 83 => [(6,3)]
  | 84 => [(7,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5)]
  | 87 => [(7,0)]
  | 88 => [(2,3)]
  | 89 => [(0,2)]
  | _ => [(1,1)]
def root8Node119Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(1,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(2,0)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(4,3)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(1,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(3,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(7,0)]
  | 88 => some [(2,3)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root8Node119Domains1_fast_eq : root8Node119Domains1 = expandDomains root8Node119Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node119Domains1 v = expandDomains root8Node119Domains1Fast v from by decide) v
theorem root8Node119Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq (by decide)
theorem root8Node119Step1Narrowing_checked :
    checkNarrowing table56 root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root8Node119Domains0 root8Node119Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node119Step1Chunk0_0_checked, root8Node119Step1Chunk0_1_checked, root8Node119Step1Chunk0_2_checked, root8Node119Step1Chunk0_3_checked, root8Node119Step1Chunk0_4_checked, root8Node119Step1Chunk0_5_checked, root8Node119Step1Chunk1_0_checked, root8Node119Step1Chunk1_1_checked, root8Node119Step1Chunk1_2_checked, root8Node119Step1Chunk1_3_checked, root8Node119Step1Chunk1_4_checked, root8Node119Step1Chunk1_5_checked, root8Node119Step1Chunk2_0_checked, root8Node119Step1Chunk2_1_checked, root8Node119Step1Chunk2_2_checked, root8Node119Step1Chunk2_3_checked, root8Node119Step1Chunk2_4_checked, root8Node119Step1Chunk2_5_checked, root8Node119Step1Chunk3_0_checked, root8Node119Step1Chunk3_1_checked, root8Node119Step1Chunk3_2_checked, root8Node119Step1Chunk3_3_checked, root8Node119Step1Chunk3_4_checked, root8Node119Step1Chunk3_5_checked, root8Node119Step1Chunk4_0_checked, root8Node119Step1Chunk4_1_checked, root8Node119Step1Chunk4_2_checked, root8Node119Step1Chunk4_3_checked, root8Node119Step1Chunk4_4_checked, root8Node119Step1Chunk4_5_checked, root8Node119Step1Chunk5_0_checked, root8Node119Step1Chunk5_1_checked, root8Node119Step1Chunk5_2_checked, root8Node119Step1Chunk5_3_checked, root8Node119Step1Chunk5_4_checked, root8Node119Step1Chunk5_5_checked, root8Node119Step1Chunk6_0_checked, root8Node119Step1Chunk6_1_checked, root8Node119Step1Chunk6_2_checked, root8Node119Step1Chunk6_3_checked, root8Node119Step1Chunk6_4_checked, root8Node119Step1Chunk6_5_checked, root8Node119Step1Chunk7_0_checked, root8Node119Step1Chunk7_1_checked, root8Node119Step1Chunk7_2_checked, root8Node119Step1Chunk7_3_checked, root8Node119Step1Chunk7_4_checked, root8Node119Step1Chunk7_5_checked, root8Node119Step1Chunk8_0_checked, root8Node119Step1Chunk8_1_checked, root8Node119Step1Chunk8_2_checked, root8Node119Step1Chunk8_3_checked, root8Node119Step1Chunk8_4_checked, root8Node119Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node119Step1_checked :
    checkReplacement table56 root8Node119Domains0 root8Node119Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node119Domains0 root8Node119Domains1
    root8Node119Domains0Fast root8Node119Domains1Fast
    root8Node119Domains0_fast_eq root8Node119Domains1_fast_eq
    root8Node119Step1Narrowing_checked (by decide)
theorem root8Node119Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node119Domains1 (.output 58) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
