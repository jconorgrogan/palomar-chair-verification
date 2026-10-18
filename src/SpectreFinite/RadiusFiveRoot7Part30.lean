module

public import SpectreFinite.RadiusFiveRoot7Part29
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable51
public import SpectreFinite.RadiusFiveTable54

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node74Domains0 : Domains 91 State := restrict root7Node72Domains2 40 (8,0)
def root7Node74Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,2)]
  | 1 => some [(7,4)]
  | 2 => some [(6,3)]
  | 3 => some [(2,2)]
  | 4 => some [(3,3)]
  | 5 => some [(5,2)]
  | 6 => some [(1,1)]
  | 7 => some [(4,1)]
  | 8 => some [(0,2)]
  | 9 => some [(1,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(8,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(8,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(1,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5),(7,5)]
  | 51 => some [(0,1),(6,4)]
  | 52 => some [(1,2),(6,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3),(6,3)]
  | 58 => some [(7,2),(8,2)]
  | 59 => some [(4,0),(5,0),(8,0)]
  | 60 => some [(4,5),(7,3)]
  | 61 => some [(0,3),(1,0)]
  | 62 => some [(2,1),(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(4,1),(8,1)]
  | 66 => some [(0,2),(6,5)]
  | 67 => some [(0,4),(1,1)]
  | 68 => some [(5,1),(5,4)]
  | 69 => some [(0,0),(0,1),(6,4)]
  | 70 => some [(0,0),(1,3),(3,3)]
  | 71 => some [(3,2),(5,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5)]
  | 75 => some [(7,0),(8,0)]
  | 76 => some [(4,3),(8,3)]
  | 77 => some [(1,5),(3,5),(5,5)]
  | 78 => some [(0,4),(6,1),(6,2)]
  | 79 => some [(5,1),(5,4),(8,4)]
  | 80 => some [(0,1),(1,4)]
  | 81 => some [(0,5),(6,2)]
  | 82 => some [(4,4),(8,4)]
  | 83 => some [(1,4)]
  | 84 => some [(0,5)]
  | 85 => some [(4,3),(7,1),(8,3)]
  | 86 => some [(7,5),(8,5)]
  | 87 => some [(1,0),(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(6,0)]
theorem root7Node74Domains0_fast_eq : root7Node74Domains0 = expandDomains root7Node74Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node74Domains0 v = expandDomains root7Node74Domains0Fast v from by decide) v
def root7Node74Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,2)]
  | 1 => [(7,4)]
  | 2 => [(6,3)]
  | 3 => [(2,2)]
  | 4 => [(3,3)]
  | 5 => [(5,2)]
  | 6 => [(1,1)]
  | 7 => [(4,1)]
  | 8 => [(0,2)]
  | 9 => [(1,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(8,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(0,3)]
  | 33 => [(8,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(5,1)]
  | 37 => [(0,1)]
  | 38 => [(6,2)]
  | 39 => [(8,4)]
  | 40 => [(8,0)]
  | 41 => [(7,3)]
  | 42 => [(4,2)]
  | 43 => [(5,3)]
  | 44 => [(8,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(8,5)]
  | 48 => [(1,0)]
  | 49 => [(7,1)]
  | 50 => [(1,5),(7,5)]
  | 51 => [(6,4)]
  | 52 => [(1,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3)]
  | 58 => [(8,2)]
  | 59 => [(4,0),(5,0),(8,0)]
  | 60 => [(4,5),(7,3)]
  | 61 => [(0,3)]
  | 62 => [(4,1)]
  | 63 => [(0,2)]
  | 64 => [(1,1)]
  | 65 => [(8,1)]
  | 66 => [(6,5)]
  | 67 => [(0,4)]
  | 68 => [(5,1),(5,4)]
  | 69 => [(0,0),(0,1),(6,4)]
  | 70 => [(1,3),(3,3)]
  | 71 => [(5,2)]
  | 72 => [(8,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5)]
  | 75 => [(7,0)]
  | 76 => [(4,3),(8,3)]
  | 77 => [(1,5),(3,5),(5,5)]
  | 78 => [(0,4),(6,2)]
  | 79 => [(5,4),(8,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(4,4)]
  | 83 => [(1,4)]
  | 84 => [(0,5)]
  | 85 => [(4,3),(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(7,5)]
  | _ => [(6,0)]
def root7Node74Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,2)]
  | 1 => some [(7,4)]
  | 2 => some [(6,3)]
  | 3 => some [(2,2)]
  | 4 => some [(3,3)]
  | 5 => some [(5,2)]
  | 6 => some [(1,1)]
  | 7 => some [(4,1)]
  | 8 => some [(0,2)]
  | 9 => some [(1,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(8,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(8,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(1,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5),(7,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(8,2)]
  | 59 => some [(4,0),(5,0),(8,0)]
  | 60 => some [(4,5),(7,3)]
  | 61 => some [(0,3)]
  | 62 => some [(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(5,1),(5,4)]
  | 69 => some [(0,0),(0,1),(6,4)]
  | 70 => some [(1,3),(3,3)]
  | 71 => some [(5,2)]
  | 72 => some [(8,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(7,0)]
  | 76 => some [(4,3),(8,3)]
  | 77 => some [(1,5),(3,5),(5,5)]
  | 78 => some [(0,4),(6,2)]
  | 79 => some [(5,4),(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(1,4)]
  | 84 => some [(0,5)]
  | 85 => some [(4,3),(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(6,0)]
theorem root7Node74Domains1_fast_eq : root7Node74Domains1 = expandDomains root7Node74Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node74Domains1 v = expandDomains root7Node74Domains1Fast v from by decide) v
theorem root7Node74Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq (by decide)
theorem root7Node74Step1Narrowing_checked :
    checkNarrowing table54 root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root7Node74Domains0 root7Node74Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node74Step1Chunk0_0_checked, root7Node74Step1Chunk0_1_checked, root7Node74Step1Chunk0_2_checked, root7Node74Step1Chunk0_3_checked, root7Node74Step1Chunk0_4_checked, root7Node74Step1Chunk0_5_checked, root7Node74Step1Chunk1_0_checked, root7Node74Step1Chunk1_1_checked, root7Node74Step1Chunk1_2_checked, root7Node74Step1Chunk1_3_checked, root7Node74Step1Chunk1_4_checked, root7Node74Step1Chunk1_5_checked, root7Node74Step1Chunk2_0_checked, root7Node74Step1Chunk2_1_checked, root7Node74Step1Chunk2_2_checked, root7Node74Step1Chunk2_3_checked, root7Node74Step1Chunk2_4_checked, root7Node74Step1Chunk2_5_checked, root7Node74Step1Chunk3_0_checked, root7Node74Step1Chunk3_1_checked, root7Node74Step1Chunk3_2_checked, root7Node74Step1Chunk3_3_checked, root7Node74Step1Chunk3_4_checked, root7Node74Step1Chunk3_5_checked, root7Node74Step1Chunk4_0_checked, root7Node74Step1Chunk4_1_checked, root7Node74Step1Chunk4_2_checked, root7Node74Step1Chunk4_3_checked, root7Node74Step1Chunk4_4_checked, root7Node74Step1Chunk4_5_checked, root7Node74Step1Chunk5_0_checked, root7Node74Step1Chunk5_1_checked, root7Node74Step1Chunk5_2_checked, root7Node74Step1Chunk5_3_checked, root7Node74Step1Chunk5_4_checked, root7Node74Step1Chunk5_5_checked, root7Node74Step1Chunk6_0_checked, root7Node74Step1Chunk6_1_checked, root7Node74Step1Chunk6_2_checked, root7Node74Step1Chunk6_3_checked, root7Node74Step1Chunk6_4_checked, root7Node74Step1Chunk6_5_checked, root7Node74Step1Chunk7_0_checked, root7Node74Step1Chunk7_1_checked, root7Node74Step1Chunk7_2_checked, root7Node74Step1Chunk7_3_checked, root7Node74Step1Chunk7_4_checked, root7Node74Step1Chunk7_5_checked, root7Node74Step1Chunk8_0_checked, root7Node74Step1Chunk8_1_checked, root7Node74Step1Chunk8_2_checked, root7Node74Step1Chunk8_3_checked, root7Node74Step1Chunk8_4_checked, root7Node74Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node74Step1_checked :
    checkReplacement table54 root7Node74Domains0 root7Node74Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node74Domains0 root7Node74Domains1
    root7Node74Domains0Fast root7Node74Domains1Fast
    root7Node74Domains0_fast_eq root7Node74Domains1_fast_eq
    root7Node74Step1Narrowing_checked (by decide)
def root7Node74Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,2)]
  | 1 => [(7,4)]
  | 2 => [(6,3)]
  | 3 => [(2,2)]
  | 4 => [(3,3)]
  | 5 => [(5,2)]
  | 6 => [(1,1)]
  | 7 => [(4,1)]
  | 8 => [(0,2)]
  | 9 => [(1,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(8,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(0,3)]
  | 33 => [(8,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(5,1)]
  | 37 => [(0,1)]
  | 38 => [(6,2)]
  | 39 => [(8,4)]
  | 40 => [(8,0)]
  | 41 => [(7,3)]
  | 42 => [(4,2)]
  | 43 => [(5,3)]
  | 44 => [(8,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(8,5)]
  | 48 => [(1,0)]
  | 49 => [(7,1)]
  | 50 => [(1,5),(7,5)]
  | 51 => [(6,4)]
  | 52 => [(1,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0),(8,0)]
  | 60 => [(4,5),(7,3)]
  | 61 => [(0,3)]
  | 62 => [(4,1)]
  | 63 => [(0,2)]
  | 64 => [(1,1)]
  | 65 => [(8,1)]
  | 66 => [(6,5)]
  | 67 => [(0,4)]
  | 68 => [(5,4)]
  | 69 => [(0,0),(6,4)]
  | 70 => [(1,3),(3,3)]
  | 71 => [(5,2)]
  | 72 => [(8,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5)]
  | 75 => [(7,0)]
  | 76 => [(4,3)]
  | 77 => [(1,5),(3,5)]
  | 78 => [(0,4),(6,2)]
  | 79 => [(5,4),(8,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(4,4)]
  | 83 => [(1,4)]
  | 84 => [(0,5)]
  | 85 => [(4,3),(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(7,5)]
  | _ => [(6,0)]
def root7Node74Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,2)]
  | 1 => some [(7,4)]
  | 2 => some [(6,3)]
  | 3 => some [(2,2)]
  | 4 => some [(3,3)]
  | 5 => some [(5,2)]
  | 6 => some [(1,1)]
  | 7 => some [(4,1)]
  | 8 => some [(0,2)]
  | 9 => some [(1,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(8,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(8,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(1,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5),(7,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0),(8,0)]
  | 60 => some [(4,5),(7,3)]
  | 61 => some [(0,3)]
  | 62 => some [(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(5,4)]
  | 69 => some [(0,0),(6,4)]
  | 70 => some [(1,3),(3,3)]
  | 71 => some [(5,2)]
  | 72 => some [(8,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(7,0)]
  | 76 => some [(4,3)]
  | 77 => some [(1,5),(3,5)]
  | 78 => some [(0,4),(6,2)]
  | 79 => some [(5,4),(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(1,4)]
  | 84 => some [(0,5)]
  | 85 => some [(4,3),(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(6,0)]
theorem root7Node74Domains2_fast_eq : root7Node74Domains2 = expandDomains root7Node74Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node74Domains2 v = expandDomains root7Node74Domains2Fast v from by decide) v
theorem root7Node74Step2Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq (by decide)
theorem root7Node74Step2Narrowing_checked :
    checkNarrowing table36 root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root7Node74Domains1 root7Node74Domains2 (by
      simp only [List.all_cons, List.all_nil, root7Node74Step2Chunk0_0_checked, root7Node74Step2Chunk0_1_checked, root7Node74Step2Chunk0_2_checked, root7Node74Step2Chunk0_3_checked, root7Node74Step2Chunk0_4_checked, root7Node74Step2Chunk0_5_checked, root7Node74Step2Chunk1_0_checked, root7Node74Step2Chunk1_1_checked, root7Node74Step2Chunk1_2_checked, root7Node74Step2Chunk1_3_checked, root7Node74Step2Chunk1_4_checked, root7Node74Step2Chunk1_5_checked, root7Node74Step2Chunk2_0_checked, root7Node74Step2Chunk2_1_checked, root7Node74Step2Chunk2_2_checked, root7Node74Step2Chunk2_3_checked, root7Node74Step2Chunk2_4_checked, root7Node74Step2Chunk2_5_checked, root7Node74Step2Chunk3_0_checked, root7Node74Step2Chunk3_1_checked, root7Node74Step2Chunk3_2_checked, root7Node74Step2Chunk3_3_checked, root7Node74Step2Chunk3_4_checked, root7Node74Step2Chunk3_5_checked, root7Node74Step2Chunk4_0_checked, root7Node74Step2Chunk4_1_checked, root7Node74Step2Chunk4_2_checked, root7Node74Step2Chunk4_3_checked, root7Node74Step2Chunk4_4_checked, root7Node74Step2Chunk4_5_checked, root7Node74Step2Chunk5_0_checked, root7Node74Step2Chunk5_1_checked, root7Node74Step2Chunk5_2_checked, root7Node74Step2Chunk5_3_checked, root7Node74Step2Chunk5_4_checked, root7Node74Step2Chunk5_5_checked, root7Node74Step2Chunk6_0_checked, root7Node74Step2Chunk6_1_checked, root7Node74Step2Chunk6_2_checked, root7Node74Step2Chunk6_3_checked, root7Node74Step2Chunk6_4_checked, root7Node74Step2Chunk6_5_checked, root7Node74Step2Chunk7_0_checked, root7Node74Step2Chunk7_1_checked, root7Node74Step2Chunk7_2_checked, root7Node74Step2Chunk7_3_checked, root7Node74Step2Chunk7_4_checked, root7Node74Step2Chunk7_5_checked, root7Node74Step2Chunk8_0_checked, root7Node74Step2Chunk8_1_checked, root7Node74Step2Chunk8_2_checked, root7Node74Step2Chunk8_3_checked, root7Node74Step2Chunk8_4_checked, root7Node74Step2Chunk8_5_checked, Bool.true_and])
theorem root7Node74Step2_checked :
    checkReplacement table36 root7Node74Domains1 root7Node74Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root7Node74Domains1 root7Node74Domains2
    root7Node74Domains1Fast root7Node74Domains2Fast
    root7Node74Domains1_fast_eq root7Node74Domains2_fast_eq
    root7Node74Step2Narrowing_checked (by decide)
def root7Node75Domains0 : Domains 91 State := restrict root7Node74Domains2 50 (1,5)
def root7Node75Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,2)]
  | 1 => some [(7,4)]
  | 2 => some [(6,3)]
  | 3 => some [(2,2)]
  | 4 => some [(3,3)]
  | 5 => some [(5,2)]
  | 6 => some [(1,1)]
  | 7 => some [(4,1)]
  | 8 => some [(0,2)]
  | 9 => some [(1,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(8,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(8,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(1,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0),(8,0)]
  | 60 => some [(4,5),(7,3)]
  | 61 => some [(0,3)]
  | 62 => some [(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(5,4)]
  | 69 => some [(0,0),(6,4)]
  | 70 => some [(1,3),(3,3)]
  | 71 => some [(5,2)]
  | 72 => some [(8,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(7,0)]
  | 76 => some [(4,3)]
  | 77 => some [(1,5),(3,5)]
  | 78 => some [(0,4),(6,2)]
  | 79 => some [(5,4),(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(1,4)]
  | 84 => some [(0,5)]
  | 85 => some [(4,3),(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(6,0)]
theorem root7Node75Domains0_fast_eq : root7Node75Domains0 = expandDomains root7Node75Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node75Domains0 v = expandDomains root7Node75Domains0Fast v from by decide) v
def root7Node75Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,2)]
  | 1 => [(7,4)]
  | 2 => [(6,3)]
  | 3 => [(2,2)]
  | 4 => [(3,3)]
  | 5 => [(5,2)]
  | 6 => [(1,1)]
  | 7 => [(4,1)]
  | 8 => [(0,2)]
  | 9 => [(1,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(8,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(0,3)]
  | 33 => [(8,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(5,1)]
  | 37 => [(0,1)]
  | 38 => [(6,2)]
  | 39 => [(8,4)]
  | 40 => [(8,0)]
  | 41 => [(7,3)]
  | 42 => [(4,2)]
  | 43 => [(5,3)]
  | 44 => [(8,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(8,5)]
  | 48 => [(1,0)]
  | 49 => [(7,1)]
  | 50 => [(1,5)]
  | 51 => [(6,4)]
  | 52 => [(1,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(0,3)]
  | 62 => [(4,1)]
  | 63 => [(0,2)]
  | 64 => [(1,1)]
  | 65 => [(8,1)]
  | 66 => [(6,5)]
  | 67 => [(0,4)]
  | 68 => [(5,4)]
  | 69 => [(0,0)]
  | 70 => [(1,3),(3,3)]
  | 71 => [(5,2)]
  | 72 => [(8,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5)]
  | 75 => [(7,0)]
  | 76 => [(4,3)]
  | 77 => [(1,5)]
  | 78 => [(0,4),(6,2)]
  | 79 => [(5,4),(8,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(4,4)]
  | 83 => [(1,4)]
  | 84 => [(0,5)]
  | 85 => [(4,3),(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(7,5)]
  | _ => [(6,0)]
def root7Node75Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,2)]
  | 1 => some [(7,4)]
  | 2 => some [(6,3)]
  | 3 => some [(2,2)]
  | 4 => some [(3,3)]
  | 5 => some [(5,2)]
  | 6 => some [(1,1)]
  | 7 => some [(4,1)]
  | 8 => some [(0,2)]
  | 9 => some [(1,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(8,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(8,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(1,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(0,3)]
  | 62 => some [(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(5,4)]
  | 69 => some [(0,0)]
  | 70 => some [(1,3),(3,3)]
  | 71 => some [(5,2)]
  | 72 => some [(8,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(7,0)]
  | 76 => some [(4,3)]
  | 77 => some [(1,5)]
  | 78 => some [(0,4),(6,2)]
  | 79 => some [(5,4),(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(1,4)]
  | 84 => some [(0,5)]
  | 85 => some [(4,3),(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(6,0)]
theorem root7Node75Domains1_fast_eq : root7Node75Domains1 = expandDomains root7Node75Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node75Domains1 v = expandDomains root7Node75Domains1Fast v from by decide) v
theorem root7Node75Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq (by decide)
theorem root7Node75Step1Narrowing_checked :
    checkNarrowing table36 root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root7Node75Domains0 root7Node75Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node75Step1Chunk0_0_checked, root7Node75Step1Chunk0_1_checked, root7Node75Step1Chunk0_2_checked, root7Node75Step1Chunk0_3_checked, root7Node75Step1Chunk0_4_checked, root7Node75Step1Chunk0_5_checked, root7Node75Step1Chunk1_0_checked, root7Node75Step1Chunk1_1_checked, root7Node75Step1Chunk1_2_checked, root7Node75Step1Chunk1_3_checked, root7Node75Step1Chunk1_4_checked, root7Node75Step1Chunk1_5_checked, root7Node75Step1Chunk2_0_checked, root7Node75Step1Chunk2_1_checked, root7Node75Step1Chunk2_2_checked, root7Node75Step1Chunk2_3_checked, root7Node75Step1Chunk2_4_checked, root7Node75Step1Chunk2_5_checked, root7Node75Step1Chunk3_0_checked, root7Node75Step1Chunk3_1_checked, root7Node75Step1Chunk3_2_checked, root7Node75Step1Chunk3_3_checked, root7Node75Step1Chunk3_4_checked, root7Node75Step1Chunk3_5_checked, root7Node75Step1Chunk4_0_checked, root7Node75Step1Chunk4_1_checked, root7Node75Step1Chunk4_2_checked, root7Node75Step1Chunk4_3_checked, root7Node75Step1Chunk4_4_checked, root7Node75Step1Chunk4_5_checked, root7Node75Step1Chunk5_0_checked, root7Node75Step1Chunk5_1_checked, root7Node75Step1Chunk5_2_checked, root7Node75Step1Chunk5_3_checked, root7Node75Step1Chunk5_4_checked, root7Node75Step1Chunk5_5_checked, root7Node75Step1Chunk6_0_checked, root7Node75Step1Chunk6_1_checked, root7Node75Step1Chunk6_2_checked, root7Node75Step1Chunk6_3_checked, root7Node75Step1Chunk6_4_checked, root7Node75Step1Chunk6_5_checked, root7Node75Step1Chunk7_0_checked, root7Node75Step1Chunk7_1_checked, root7Node75Step1Chunk7_2_checked, root7Node75Step1Chunk7_3_checked, root7Node75Step1Chunk7_4_checked, root7Node75Step1Chunk7_5_checked, root7Node75Step1Chunk8_0_checked, root7Node75Step1Chunk8_1_checked, root7Node75Step1Chunk8_2_checked, root7Node75Step1Chunk8_3_checked, root7Node75Step1Chunk8_4_checked, root7Node75Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node75Step1_checked :
    checkReplacement table36 root7Node75Domains0 root7Node75Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node75Domains0 root7Node75Domains1
    root7Node75Domains0Fast root7Node75Domains1Fast
    root7Node75Domains0_fast_eq root7Node75Domains1_fast_eq
    root7Node75Step1Narrowing_checked (by decide)
def root7Node76Domains0 : Domains 91 State := restrict root7Node75Domains1 70 (1,3)
def root7Node76Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,2)]
  | 1 => some [(7,4)]
  | 2 => some [(6,3)]
  | 3 => some [(2,2)]
  | 4 => some [(3,3)]
  | 5 => some [(5,2)]
  | 6 => some [(1,1)]
  | 7 => some [(4,1)]
  | 8 => some [(0,2)]
  | 9 => some [(1,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(8,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(8,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(1,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(0,3)]
  | 62 => some [(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(5,4)]
  | 69 => some [(0,0)]
  | 70 => some [(1,3)]
  | 71 => some [(5,2)]
  | 72 => some [(8,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(7,0)]
  | 76 => some [(4,3)]
  | 77 => some [(1,5)]
  | 78 => some [(0,4),(6,2)]
  | 79 => some [(5,4),(8,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(1,4)]
  | 84 => some [(0,5)]
  | 85 => some [(4,3),(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(6,0)]
theorem root7Node76Domains0_fast_eq : root7Node76Domains0 = expandDomains root7Node76Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node76Domains0 v = expandDomains root7Node76Domains0Fast v from by decide) v
def root7Node76Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,2)]
  | 1 => [(7,4)]
  | 2 => [(6,3)]
  | 3 => [(2,2)]
  | 4 => [(3,3)]
  | 5 => [(5,2)]
  | 6 => [(1,1)]
  | 7 => [(4,1)]
  | 8 => [(0,2)]
  | 9 => [(1,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(8,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(0,3)]
  | 33 => [(8,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(5,1)]
  | 37 => [(0,1)]
  | 38 => [(6,2)]
  | 39 => [(8,4)]
  | 40 => [(8,0)]
  | 41 => [(7,3)]
  | 42 => [(4,2)]
  | 43 => [(5,3)]
  | 44 => [(8,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(8,5)]
  | 48 => [(1,0)]
  | 49 => [(7,1)]
  | 50 => [(1,5)]
  | 51 => [(6,4)]
  | 52 => [(1,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(0,3)]
  | 62 => [(4,1)]
  | 63 => [(0,2)]
  | 64 => [(1,1)]
  | 65 => [(8,1)]
  | 66 => [(6,5)]
  | 67 => [(0,4)]
  | 68 => [(5,4)]
  | 69 => [(0,0)]
  | 70 => [(1,3)]
  | 71 => [(5,2)]
  | 72 => [(8,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5)]
  | 75 => [(7,0)]
  | 76 => [(4,3)]
  | 77 => [(1,5)]
  | 78 => [(0,4)]
  | 79 => [(5,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(4,4)]
  | 83 => [(1,4)]
  | 84 => [(0,5)]
  | 85 => [(4,3)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(7,5)]
  | _ => [(6,0)]
def root7Node76Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,2)]
  | 1 => some [(7,4)]
  | 2 => some [(6,3)]
  | 3 => some [(2,2)]
  | 4 => some [(3,3)]
  | 5 => some [(5,2)]
  | 6 => some [(1,1)]
  | 7 => some [(4,1)]
  | 8 => some [(0,2)]
  | 9 => some [(1,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(8,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(8,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(1,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(0,3)]
  | 62 => some [(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(5,4)]
  | 69 => some [(0,0)]
  | 70 => some [(1,3)]
  | 71 => some [(5,2)]
  | 72 => some [(8,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(7,0)]
  | 76 => some [(4,3)]
  | 77 => some [(1,5)]
  | 78 => some [(0,4)]
  | 79 => some [(5,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(1,4)]
  | 84 => some [(0,5)]
  | 85 => some [(4,3)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(6,0)]
theorem root7Node76Domains1_fast_eq : root7Node76Domains1 = expandDomains root7Node76Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node76Domains1 v = expandDomains root7Node76Domains1Fast v from by decide) v
theorem root7Node76Step1Chunk0_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_0⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk0_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_1⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk0_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_2⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk0_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_3⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk0_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_4⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk0_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_5⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk1_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_0⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk1_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_1⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk1_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_2⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk1_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_3⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk1_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_4⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk1_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_5⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk2_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_0⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk2_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_1⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk2_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_2⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk2_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_3⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk2_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_4⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk2_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_5⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk3_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_0⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk3_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_1⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk3_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_2⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk3_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_3⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk3_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_4⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk3_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_5⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk4_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_0⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk4_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_1⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk4_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_2⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk4_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_3⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk4_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_4⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk4_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_5⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk5_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_0⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk5_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_1⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk5_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_2⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk5_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_3⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk5_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_4⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk5_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_5⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk6_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_0⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk6_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_1⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk6_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_2⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk6_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_3⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk6_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_4⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk6_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_5⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk7_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_0⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk7_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_1⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk7_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_2⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk7_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_3⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk7_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_4⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk7_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_5⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk8_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_0⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk8_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_1⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk8_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_2⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk8_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_3⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk8_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_4⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Chunk8_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_5⟩
      root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq (by decide)
theorem root7Node76Step1Narrowing_checked :
    checkNarrowing table51 root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkNarrowing_flatten table51Scope [table51Rows0_0,table51Rows0_1,table51Rows0_2,table51Rows0_3,table51Rows0_4,table51Rows0_5,table51Rows1_0,table51Rows1_1,table51Rows1_2,table51Rows1_3,table51Rows1_4,table51Rows1_5,table51Rows2_0,table51Rows2_1,table51Rows2_2,table51Rows2_3,table51Rows2_4,table51Rows2_5,table51Rows3_0,table51Rows3_1,table51Rows3_2,table51Rows3_3,table51Rows3_4,table51Rows3_5,table51Rows4_0,table51Rows4_1,table51Rows4_2,table51Rows4_3,table51Rows4_4,table51Rows4_5,table51Rows5_0,table51Rows5_1,table51Rows5_2,table51Rows5_3,table51Rows5_4,table51Rows5_5,table51Rows6_0,table51Rows6_1,table51Rows6_2,table51Rows6_3,table51Rows6_4,table51Rows6_5,table51Rows7_0,table51Rows7_1,table51Rows7_2,table51Rows7_3,table51Rows7_4,table51Rows7_5,table51Rows8_0,table51Rows8_1,table51Rows8_2,table51Rows8_3,table51Rows8_4,table51Rows8_5]
    root7Node76Domains0 root7Node76Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node76Step1Chunk0_0_checked, root7Node76Step1Chunk0_1_checked, root7Node76Step1Chunk0_2_checked, root7Node76Step1Chunk0_3_checked, root7Node76Step1Chunk0_4_checked, root7Node76Step1Chunk0_5_checked, root7Node76Step1Chunk1_0_checked, root7Node76Step1Chunk1_1_checked, root7Node76Step1Chunk1_2_checked, root7Node76Step1Chunk1_3_checked, root7Node76Step1Chunk1_4_checked, root7Node76Step1Chunk1_5_checked, root7Node76Step1Chunk2_0_checked, root7Node76Step1Chunk2_1_checked, root7Node76Step1Chunk2_2_checked, root7Node76Step1Chunk2_3_checked, root7Node76Step1Chunk2_4_checked, root7Node76Step1Chunk2_5_checked, root7Node76Step1Chunk3_0_checked, root7Node76Step1Chunk3_1_checked, root7Node76Step1Chunk3_2_checked, root7Node76Step1Chunk3_3_checked, root7Node76Step1Chunk3_4_checked, root7Node76Step1Chunk3_5_checked, root7Node76Step1Chunk4_0_checked, root7Node76Step1Chunk4_1_checked, root7Node76Step1Chunk4_2_checked, root7Node76Step1Chunk4_3_checked, root7Node76Step1Chunk4_4_checked, root7Node76Step1Chunk4_5_checked, root7Node76Step1Chunk5_0_checked, root7Node76Step1Chunk5_1_checked, root7Node76Step1Chunk5_2_checked, root7Node76Step1Chunk5_3_checked, root7Node76Step1Chunk5_4_checked, root7Node76Step1Chunk5_5_checked, root7Node76Step1Chunk6_0_checked, root7Node76Step1Chunk6_1_checked, root7Node76Step1Chunk6_2_checked, root7Node76Step1Chunk6_3_checked, root7Node76Step1Chunk6_4_checked, root7Node76Step1Chunk6_5_checked, root7Node76Step1Chunk7_0_checked, root7Node76Step1Chunk7_1_checked, root7Node76Step1Chunk7_2_checked, root7Node76Step1Chunk7_3_checked, root7Node76Step1Chunk7_4_checked, root7Node76Step1Chunk7_5_checked, root7Node76Step1Chunk8_0_checked, root7Node76Step1Chunk8_1_checked, root7Node76Step1Chunk8_2_checked, root7Node76Step1Chunk8_3_checked, root7Node76Step1Chunk8_4_checked, root7Node76Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node76Step1_checked :
    checkReplacement table51 root7Node76Domains0 root7Node76Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node76Domains0 root7Node76Domains1
    root7Node76Domains0Fast root7Node76Domains1Fast
    root7Node76Domains0_fast_eq root7Node76Domains1_fast_eq
    root7Node76Step1Narrowing_checked (by decide)
theorem root7Node76Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node76Domains1 (.output 36) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
