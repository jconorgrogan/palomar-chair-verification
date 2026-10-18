module

public import SpectreFinite.RadiusFiveRoot7Part62
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node158Domains0 : Domains 91 State := restrict root7Node154Domains1 21 (8,4)
def root7Node158Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(5,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2),(8,2)]
  | 30 => some [(4,3),(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(7,4),(8,4)]
  | 40 => some [(4,0),(7,4),(8,0)]
  | 41 => some [(1,3),(7,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(3,5),(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(1,5)]
  | 51 => some [(0,1),(6,4),(6,5)]
  | 52 => some [(0,4),(1,2),(6,2)]
  | 53 => some [(1,4),(3,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(1,3),(6,3)]
  | 58 => some [(2,2),(2,4),(4,2)]
  | 59 => some [(1,3),(3,3),(5,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(0,3),(1,0),(3,0),(7,0)]
  | 62 => some [(2,1),(2,3),(2,5),(4,1)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(1,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(7,1)]
  | 68 => some [(0,1),(1,4),(3,4),(6,5)]
  | 69 => some [(0,4),(0,5),(6,2),(6,3)]
  | 70 => some [(0,0),(1,3),(3,3),(6,4)]
  | 71 => some [(1,2),(3,2),(5,2),(7,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5),(8,2)]
  | 75 => some [(3,0),(5,0),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5)]
  | 77 => some [(0,2),(1,0),(6,0),(7,0)]
  | 78 => some [(0,3),(0,4),(6,1),(6,2)]
  | 79 => some [(5,1),(5,4),(8,4)]
  | 80 => some [(0,1),(1,4),(6,4)]
  | 81 => some [(0,5),(1,2),(6,2)]
  | 82 => some [(4,4),(8,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(4,3),(5,3),(7,1),(8,3)]
  | 86 => some [(7,5),(8,5)]
  | 87 => some [(0,3),(1,0),(6,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node158Domains0_fast_eq : root7Node158Domains0 = expandDomains root7Node158Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node158Domains0 v = expandDomains root7Node158Domains0Fast v from by decide) v
def root7Node158Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(5,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(5,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(8,0)]
  | 14 => [(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(4,2),(8,2)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(0,3)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(7,4),(8,4)]
  | 40 => [(4,0),(8,0)]
  | 41 => [(7,3)]
  | 42 => [(4,2)]
  | 43 => [(5,3)]
  | 44 => [(8,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(4,1),(8,1)]
  | 50 => [(0,2),(1,5)]
  | 51 => [(0,1),(6,4)]
  | 52 => [(1,2),(6,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3),(6,3)]
  | 58 => [(2,2),(4,2)]
  | 59 => [(1,3),(3,3),(5,3)]
  | 60 => [(5,2),(5,5),(8,5)]
  | 61 => [(0,3),(1,0)]
  | 62 => [(2,1),(4,1)]
  | 63 => [(0,2)]
  | 64 => [(1,1)]
  | 65 => [(4,1),(8,1)]
  | 66 => [(0,2),(6,5)]
  | 67 => [(0,4),(1,1)]
  | 68 => [(0,1),(1,4),(3,4),(6,5)]
  | 69 => [(0,4),(0,5),(6,2),(6,3)]
  | 70 => [(0,0),(1,3),(3,3)]
  | 71 => [(3,2),(5,2)]
  | 72 => [(4,0),(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(5,2),(5,5)]
  | 75 => [(3,0),(5,0),(7,0)]
  | 76 => [(2,3),(2,5),(4,5)]
  | 77 => [(0,2),(1,0),(6,0),(7,0)]
  | 78 => [(0,4),(6,1),(6,2)]
  | 79 => [(5,1),(5,4),(8,4)]
  | 80 => [(0,1),(1,4),(6,4)]
  | 81 => [(0,5),(1,2),(6,2)]
  | 82 => [(4,4),(8,4)]
  | 83 => [(0,0),(6,4)]
  | 84 => [(1,2),(7,2)]
  | 85 => [(4,3),(7,1),(8,3)]
  | 86 => [(7,5),(8,5)]
  | 87 => [(0,3),(1,0),(6,0)]
  | 88 => [(7,1),(8,1)]
  | 89 => [(1,5),(7,5)]
  | _ => [(0,3),(6,1)]
def root7Node158Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(5,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2),(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(7,4),(8,4)]
  | 40 => some [(4,0),(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(1,5)]
  | 51 => some [(0,1),(6,4)]
  | 52 => some [(1,2),(6,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3),(6,3)]
  | 58 => some [(2,2),(4,2)]
  | 59 => some [(1,3),(3,3),(5,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(0,3),(1,0)]
  | 62 => some [(2,1),(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(4,1),(8,1)]
  | 66 => some [(0,2),(6,5)]
  | 67 => some [(0,4),(1,1)]
  | 68 => some [(0,1),(1,4),(3,4),(6,5)]
  | 69 => some [(0,4),(0,5),(6,2),(6,3)]
  | 70 => some [(0,0),(1,3),(3,3)]
  | 71 => some [(3,2),(5,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5)]
  | 75 => some [(3,0),(5,0),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5)]
  | 77 => some [(0,2),(1,0),(6,0),(7,0)]
  | 78 => some [(0,4),(6,1),(6,2)]
  | 79 => some [(5,1),(5,4),(8,4)]
  | 80 => some [(0,1),(1,4),(6,4)]
  | 81 => some [(0,5),(1,2),(6,2)]
  | 82 => some [(4,4),(8,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(4,3),(7,1),(8,3)]
  | 86 => some [(7,5),(8,5)]
  | 87 => some [(0,3),(1,0),(6,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node158Domains1_fast_eq : root7Node158Domains1 = expandDomains root7Node158Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node158Domains1 v = expandDomains root7Node158Domains1Fast v from by decide) v
theorem root7Node158Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq (by decide)
theorem root7Node158Step1Narrowing_checked :
    checkNarrowing table54 root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root7Node158Domains0 root7Node158Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node158Step1Chunk0_0_checked, root7Node158Step1Chunk0_1_checked, root7Node158Step1Chunk0_2_checked, root7Node158Step1Chunk0_3_checked, root7Node158Step1Chunk0_4_checked, root7Node158Step1Chunk0_5_checked, root7Node158Step1Chunk1_0_checked, root7Node158Step1Chunk1_1_checked, root7Node158Step1Chunk1_2_checked, root7Node158Step1Chunk1_3_checked, root7Node158Step1Chunk1_4_checked, root7Node158Step1Chunk1_5_checked, root7Node158Step1Chunk2_0_checked, root7Node158Step1Chunk2_1_checked, root7Node158Step1Chunk2_2_checked, root7Node158Step1Chunk2_3_checked, root7Node158Step1Chunk2_4_checked, root7Node158Step1Chunk2_5_checked, root7Node158Step1Chunk3_0_checked, root7Node158Step1Chunk3_1_checked, root7Node158Step1Chunk3_2_checked, root7Node158Step1Chunk3_3_checked, root7Node158Step1Chunk3_4_checked, root7Node158Step1Chunk3_5_checked, root7Node158Step1Chunk4_0_checked, root7Node158Step1Chunk4_1_checked, root7Node158Step1Chunk4_2_checked, root7Node158Step1Chunk4_3_checked, root7Node158Step1Chunk4_4_checked, root7Node158Step1Chunk4_5_checked, root7Node158Step1Chunk5_0_checked, root7Node158Step1Chunk5_1_checked, root7Node158Step1Chunk5_2_checked, root7Node158Step1Chunk5_3_checked, root7Node158Step1Chunk5_4_checked, root7Node158Step1Chunk5_5_checked, root7Node158Step1Chunk6_0_checked, root7Node158Step1Chunk6_1_checked, root7Node158Step1Chunk6_2_checked, root7Node158Step1Chunk6_3_checked, root7Node158Step1Chunk6_4_checked, root7Node158Step1Chunk6_5_checked, root7Node158Step1Chunk7_0_checked, root7Node158Step1Chunk7_1_checked, root7Node158Step1Chunk7_2_checked, root7Node158Step1Chunk7_3_checked, root7Node158Step1Chunk7_4_checked, root7Node158Step1Chunk7_5_checked, root7Node158Step1Chunk8_0_checked, root7Node158Step1Chunk8_1_checked, root7Node158Step1Chunk8_2_checked, root7Node158Step1Chunk8_3_checked, root7Node158Step1Chunk8_4_checked, root7Node158Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node158Step1_checked :
    checkReplacement table54 root7Node158Domains0 root7Node158Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node158Domains0 root7Node158Domains1
    root7Node158Domains0Fast root7Node158Domains1Fast
    root7Node158Domains0_fast_eq root7Node158Domains1_fast_eq
    root7Node158Step1Narrowing_checked (by decide)
def root7Node158Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(5,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(5,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(8,0)]
  | 14 => [(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(4,2),(8,2)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(0,3)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(7,4),(8,4)]
  | 40 => [(4,0),(8,0)]
  | 41 => [(7,3)]
  | 42 => [(4,2)]
  | 43 => [(5,3)]
  | 44 => [(8,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(4,1),(8,1)]
  | 50 => [(0,2),(1,5)]
  | 51 => [(0,1),(6,4)]
  | 52 => [(1,2),(6,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3),(6,3)]
  | 58 => [(2,2),(4,2)]
  | 59 => [(3,3),(5,3)]
  | 60 => [(5,2),(5,5),(8,5)]
  | 61 => [(0,3),(1,0)]
  | 62 => [(2,1),(4,1)]
  | 63 => [(0,2)]
  | 64 => [(1,1)]
  | 65 => [(4,1),(8,1)]
  | 66 => [(0,2),(6,5)]
  | 67 => [(0,4),(1,1)]
  | 68 => [(0,1),(1,4),(3,4)]
  | 69 => [(0,5),(6,2),(6,3)]
  | 70 => [(0,0),(1,3),(3,3)]
  | 71 => [(3,2),(5,2)]
  | 72 => [(4,0),(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(5,2),(5,5)]
  | 75 => [(3,0),(5,0),(7,0)]
  | 76 => [(2,3),(2,5),(4,5)]
  | 77 => [(0,2),(1,0),(6,0)]
  | 78 => [(0,4),(6,1),(6,2)]
  | 79 => [(5,1),(5,4),(8,4)]
  | 80 => [(0,1),(1,4),(6,4)]
  | 81 => [(0,5),(1,2),(6,2)]
  | 82 => [(4,4),(8,4)]
  | 83 => [(0,0),(6,4)]
  | 84 => [(1,2),(7,2)]
  | 85 => [(4,3),(7,1),(8,3)]
  | 86 => [(7,5),(8,5)]
  | 87 => [(0,3),(1,0),(6,0)]
  | 88 => [(7,1),(8,1)]
  | 89 => [(1,5),(7,5)]
  | _ => [(0,3),(6,1)]
def root7Node158Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(5,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2),(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(7,4),(8,4)]
  | 40 => some [(4,0),(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(1,5)]
  | 51 => some [(0,1),(6,4)]
  | 52 => some [(1,2),(6,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3),(6,3)]
  | 58 => some [(2,2),(4,2)]
  | 59 => some [(3,3),(5,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(0,3),(1,0)]
  | 62 => some [(2,1),(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(4,1),(8,1)]
  | 66 => some [(0,2),(6,5)]
  | 67 => some [(0,4),(1,1)]
  | 68 => some [(0,1),(1,4),(3,4)]
  | 69 => some [(0,5),(6,2),(6,3)]
  | 70 => some [(0,0),(1,3),(3,3)]
  | 71 => some [(3,2),(5,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5)]
  | 75 => some [(3,0),(5,0),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5)]
  | 77 => some [(0,2),(1,0),(6,0)]
  | 78 => some [(0,4),(6,1),(6,2)]
  | 79 => some [(5,1),(5,4),(8,4)]
  | 80 => some [(0,1),(1,4),(6,4)]
  | 81 => some [(0,5),(1,2),(6,2)]
  | 82 => some [(4,4),(8,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(4,3),(7,1),(8,3)]
  | 86 => some [(7,5),(8,5)]
  | 87 => some [(0,3),(1,0),(6,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node158Domains2_fast_eq : root7Node158Domains2 = expandDomains root7Node158Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node158Domains2 v = expandDomains root7Node158Domains2Fast v from by decide) v
theorem root7Node158Step2Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq (by decide)
theorem root7Node158Step2Narrowing_checked :
    checkNarrowing table36 root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root7Node158Domains1 root7Node158Domains2 (by
      simp only [List.all_cons, List.all_nil, root7Node158Step2Chunk0_0_checked, root7Node158Step2Chunk0_1_checked, root7Node158Step2Chunk0_2_checked, root7Node158Step2Chunk0_3_checked, root7Node158Step2Chunk0_4_checked, root7Node158Step2Chunk0_5_checked, root7Node158Step2Chunk1_0_checked, root7Node158Step2Chunk1_1_checked, root7Node158Step2Chunk1_2_checked, root7Node158Step2Chunk1_3_checked, root7Node158Step2Chunk1_4_checked, root7Node158Step2Chunk1_5_checked, root7Node158Step2Chunk2_0_checked, root7Node158Step2Chunk2_1_checked, root7Node158Step2Chunk2_2_checked, root7Node158Step2Chunk2_3_checked, root7Node158Step2Chunk2_4_checked, root7Node158Step2Chunk2_5_checked, root7Node158Step2Chunk3_0_checked, root7Node158Step2Chunk3_1_checked, root7Node158Step2Chunk3_2_checked, root7Node158Step2Chunk3_3_checked, root7Node158Step2Chunk3_4_checked, root7Node158Step2Chunk3_5_checked, root7Node158Step2Chunk4_0_checked, root7Node158Step2Chunk4_1_checked, root7Node158Step2Chunk4_2_checked, root7Node158Step2Chunk4_3_checked, root7Node158Step2Chunk4_4_checked, root7Node158Step2Chunk4_5_checked, root7Node158Step2Chunk5_0_checked, root7Node158Step2Chunk5_1_checked, root7Node158Step2Chunk5_2_checked, root7Node158Step2Chunk5_3_checked, root7Node158Step2Chunk5_4_checked, root7Node158Step2Chunk5_5_checked, root7Node158Step2Chunk6_0_checked, root7Node158Step2Chunk6_1_checked, root7Node158Step2Chunk6_2_checked, root7Node158Step2Chunk6_3_checked, root7Node158Step2Chunk6_4_checked, root7Node158Step2Chunk6_5_checked, root7Node158Step2Chunk7_0_checked, root7Node158Step2Chunk7_1_checked, root7Node158Step2Chunk7_2_checked, root7Node158Step2Chunk7_3_checked, root7Node158Step2Chunk7_4_checked, root7Node158Step2Chunk7_5_checked, root7Node158Step2Chunk8_0_checked, root7Node158Step2Chunk8_1_checked, root7Node158Step2Chunk8_2_checked, root7Node158Step2Chunk8_3_checked, root7Node158Step2Chunk8_4_checked, root7Node158Step2Chunk8_5_checked, Bool.true_and])
theorem root7Node158Step2_checked :
    checkReplacement table36 root7Node158Domains1 root7Node158Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root7Node158Domains1 root7Node158Domains2
    root7Node158Domains1Fast root7Node158Domains2Fast
    root7Node158Domains1_fast_eq root7Node158Domains2_fast_eq
    root7Node158Step2Narrowing_checked (by decide)
def root7Node159Domains0 : Domains 91 State := restrict root7Node158Domains2 29 (4,2)
def root7Node159Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(5,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(7,4),(8,4)]
  | 40 => some [(4,0),(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(1,5)]
  | 51 => some [(0,1),(6,4)]
  | 52 => some [(1,2),(6,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3),(6,3)]
  | 58 => some [(2,2),(4,2)]
  | 59 => some [(3,3),(5,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(0,3),(1,0)]
  | 62 => some [(2,1),(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(4,1),(8,1)]
  | 66 => some [(0,2),(6,5)]
  | 67 => some [(0,4),(1,1)]
  | 68 => some [(0,1),(1,4),(3,4)]
  | 69 => some [(0,5),(6,2),(6,3)]
  | 70 => some [(0,0),(1,3),(3,3)]
  | 71 => some [(3,2),(5,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5)]
  | 75 => some [(3,0),(5,0),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5)]
  | 77 => some [(0,2),(1,0),(6,0)]
  | 78 => some [(0,4),(6,1),(6,2)]
  | 79 => some [(5,1),(5,4),(8,4)]
  | 80 => some [(0,1),(1,4),(6,4)]
  | 81 => some [(0,5),(1,2),(6,2)]
  | 82 => some [(4,4),(8,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(4,3),(7,1),(8,3)]
  | 86 => some [(7,5),(8,5)]
  | 87 => some [(0,3),(1,0),(6,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node159Domains0_fast_eq : root7Node159Domains0 = expandDomains root7Node159Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node159Domains0 v = expandDomains root7Node159Domains0Fast v from by decide) v
def root7Node159Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(5,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(5,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(8,0)]
  | 14 => [(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(4,2)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(0,3)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(7,4)]
  | 40 => [(4,0),(8,0)]
  | 41 => [(7,3)]
  | 42 => [(4,2)]
  | 43 => [(5,3)]
  | 44 => [(8,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(4,1)]
  | 50 => [(0,2)]
  | 51 => [(0,1),(6,4)]
  | 52 => [(1,2),(6,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(6,3)]
  | 58 => [(2,2)]
  | 59 => [(3,3)]
  | 60 => [(5,2)]
  | 61 => [(0,3),(1,0)]
  | 62 => [(2,1),(4,1)]
  | 63 => [(0,2)]
  | 64 => [(1,1)]
  | 65 => [(4,1)]
  | 66 => [(0,2)]
  | 67 => [(1,1)]
  | 68 => [(0,1)]
  | 69 => [(6,2)]
  | 70 => [(0,0),(1,3),(3,3)]
  | 71 => [(3,2),(5,2)]
  | 72 => [(4,0),(8,0)]
  | 73 => [(7,3)]
  | 74 => [(5,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(1,0)]
  | 78 => [(0,4),(6,1),(6,2)]
  | 79 => [(5,1),(5,4),(8,4)]
  | 80 => [(0,1),(6,4)]
  | 81 => [(1,2),(6,2)]
  | 82 => [(8,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(4,3),(7,1),(8,3)]
  | 86 => [(7,5),(8,5)]
  | 87 => [(0,3),(1,0)]
  | 88 => [(7,1),(8,1)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root7Node159Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(5,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(7,4)]
  | 40 => some [(4,0),(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,1),(6,4)]
  | 52 => some [(1,2),(6,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(6,3)]
  | 58 => some [(2,2)]
  | 59 => some [(3,3)]
  | 60 => some [(5,2)]
  | 61 => some [(0,3),(1,0)]
  | 62 => some [(2,1),(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(4,1)]
  | 66 => some [(0,2)]
  | 67 => some [(1,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(0,0),(1,3),(3,3)]
  | 71 => some [(3,2),(5,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(5,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(1,0)]
  | 78 => some [(0,4),(6,1),(6,2)]
  | 79 => some [(5,1),(5,4),(8,4)]
  | 80 => some [(0,1),(6,4)]
  | 81 => some [(1,2),(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(7,1),(8,3)]
  | 86 => some [(7,5),(8,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root7Node159Domains1_fast_eq : root7Node159Domains1 = expandDomains root7Node159Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node159Domains1 v = expandDomains root7Node159Domains1Fast v from by decide) v
theorem root7Node159Step1Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq (by decide)
theorem root7Node159Step1Narrowing_checked :
    checkNarrowing table57 root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root7Node159Domains0 root7Node159Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node159Step1Chunk0_0_checked, root7Node159Step1Chunk0_1_checked, root7Node159Step1Chunk0_2_checked, root7Node159Step1Chunk0_3_checked, root7Node159Step1Chunk0_4_checked, root7Node159Step1Chunk0_5_checked, root7Node159Step1Chunk1_0_checked, root7Node159Step1Chunk1_1_checked, root7Node159Step1Chunk1_2_checked, root7Node159Step1Chunk1_3_checked, root7Node159Step1Chunk1_4_checked, root7Node159Step1Chunk1_5_checked, root7Node159Step1Chunk2_0_checked, root7Node159Step1Chunk2_1_checked, root7Node159Step1Chunk2_2_checked, root7Node159Step1Chunk2_3_checked, root7Node159Step1Chunk2_4_checked, root7Node159Step1Chunk2_5_checked, root7Node159Step1Chunk3_0_checked, root7Node159Step1Chunk3_1_checked, root7Node159Step1Chunk3_2_checked, root7Node159Step1Chunk3_3_checked, root7Node159Step1Chunk3_4_checked, root7Node159Step1Chunk3_5_checked, root7Node159Step1Chunk4_0_checked, root7Node159Step1Chunk4_1_checked, root7Node159Step1Chunk4_2_checked, root7Node159Step1Chunk4_3_checked, root7Node159Step1Chunk4_4_checked, root7Node159Step1Chunk4_5_checked, root7Node159Step1Chunk5_0_checked, root7Node159Step1Chunk5_1_checked, root7Node159Step1Chunk5_2_checked, root7Node159Step1Chunk5_3_checked, root7Node159Step1Chunk5_4_checked, root7Node159Step1Chunk5_5_checked, root7Node159Step1Chunk6_0_checked, root7Node159Step1Chunk6_1_checked, root7Node159Step1Chunk6_2_checked, root7Node159Step1Chunk6_3_checked, root7Node159Step1Chunk6_4_checked, root7Node159Step1Chunk6_5_checked, root7Node159Step1Chunk7_0_checked, root7Node159Step1Chunk7_1_checked, root7Node159Step1Chunk7_2_checked, root7Node159Step1Chunk7_3_checked, root7Node159Step1Chunk7_4_checked, root7Node159Step1Chunk7_5_checked, root7Node159Step1Chunk8_0_checked, root7Node159Step1Chunk8_1_checked, root7Node159Step1Chunk8_2_checked, root7Node159Step1Chunk8_3_checked, root7Node159Step1Chunk8_4_checked, root7Node159Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node159Step1_checked :
    checkReplacement table57 root7Node159Domains0 root7Node159Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node159Domains0 root7Node159Domains1
    root7Node159Domains0Fast root7Node159Domains1Fast
    root7Node159Domains0_fast_eq root7Node159Domains1_fast_eq
    root7Node159Step1Narrowing_checked (by decide)
def root7Node160Domains0 : Domains 91 State := restrict root7Node159Domains1 40 (4,0)
def root7Node160Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(5,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(7,4)]
  | 40 => some [(4,0)]
  | 41 => some [(7,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,1),(6,4)]
  | 52 => some [(1,2),(6,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(6,3)]
  | 58 => some [(2,2)]
  | 59 => some [(3,3)]
  | 60 => some [(5,2)]
  | 61 => some [(0,3),(1,0)]
  | 62 => some [(2,1),(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(4,1)]
  | 66 => some [(0,2)]
  | 67 => some [(1,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(0,0),(1,3),(3,3)]
  | 71 => some [(3,2),(5,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(5,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(1,0)]
  | 78 => some [(0,4),(6,1),(6,2)]
  | 79 => some [(5,1),(5,4),(8,4)]
  | 80 => some [(0,1),(6,4)]
  | 81 => some [(1,2),(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(7,1),(8,3)]
  | 86 => some [(7,5),(8,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root7Node160Domains0_fast_eq : root7Node160Domains0 = expandDomains root7Node160Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node160Domains0 v = expandDomains root7Node160Domains0Fast v from by decide) v
def root7Node160Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(5,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(5,1)]
  | 10 => [(0,1)]
  | 11 => [(6,2)]
  | 12 => [(8,4)]
  | 13 => [(8,0)]
  | 14 => [(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(4,2)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(0,3)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(7,4)]
  | 40 => [(4,0)]
  | 41 => [(7,3)]
  | 42 => [(4,2)]
  | 43 => [(5,3)]
  | 44 => [(8,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(4,1)]
  | 50 => [(0,2)]
  | 51 => [(0,1)]
  | 52 => [(6,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(6,3)]
  | 58 => [(2,2)]
  | 59 => [(3,3)]
  | 60 => [(5,2)]
  | 61 => [(1,0)]
  | 62 => [(2,1)]
  | 63 => [(0,2)]
  | 64 => [(1,1)]
  | 65 => [(4,1)]
  | 66 => [(0,2)]
  | 67 => [(1,1)]
  | 68 => [(0,1)]
  | 69 => [(6,2)]
  | 70 => [(0,0)]
  | 71 => [(3,2)]
  | 72 => [(4,0)]
  | 73 => [(7,3)]
  | 74 => [(5,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(1,0)]
  | 78 => [(6,1)]
  | 79 => [(5,1)]
  | 80 => [(0,1)]
  | 81 => [(6,2)]
  | 82 => [(8,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(8,3)]
  | 86 => [(8,5)]
  | 87 => [(1,0)]
  | 88 => [(7,1)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root7Node160Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(5,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(5,1)]
  | 10 => some [(0,1)]
  | 11 => some [(6,2)]
  | 12 => some [(8,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(7,4)]
  | 40 => some [(4,0)]
  | 41 => some [(7,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,1)]
  | 52 => some [(6,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(6,3)]
  | 58 => some [(2,2)]
  | 59 => some [(3,3)]
  | 60 => some [(5,2)]
  | 61 => some [(1,0)]
  | 62 => some [(2,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(4,1)]
  | 66 => some [(0,2)]
  | 67 => some [(1,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(0,0)]
  | 71 => some [(3,2)]
  | 72 => some [(4,0)]
  | 73 => some [(7,3)]
  | 74 => some [(5,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(1,0)]
  | 78 => some [(6,1)]
  | 79 => some [(5,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(8,5)]
  | 87 => some [(1,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root7Node160Domains1_fast_eq : root7Node160Domains1 = expandDomains root7Node160Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node160Domains1 v = expandDomains root7Node160Domains1Fast v from by decide) v
theorem root7Node160Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq (by decide)
theorem root7Node160Step1Narrowing_checked :
    checkNarrowing table54 root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root7Node160Domains0 root7Node160Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node160Step1Chunk0_0_checked, root7Node160Step1Chunk0_1_checked, root7Node160Step1Chunk0_2_checked, root7Node160Step1Chunk0_3_checked, root7Node160Step1Chunk0_4_checked, root7Node160Step1Chunk0_5_checked, root7Node160Step1Chunk1_0_checked, root7Node160Step1Chunk1_1_checked, root7Node160Step1Chunk1_2_checked, root7Node160Step1Chunk1_3_checked, root7Node160Step1Chunk1_4_checked, root7Node160Step1Chunk1_5_checked, root7Node160Step1Chunk2_0_checked, root7Node160Step1Chunk2_1_checked, root7Node160Step1Chunk2_2_checked, root7Node160Step1Chunk2_3_checked, root7Node160Step1Chunk2_4_checked, root7Node160Step1Chunk2_5_checked, root7Node160Step1Chunk3_0_checked, root7Node160Step1Chunk3_1_checked, root7Node160Step1Chunk3_2_checked, root7Node160Step1Chunk3_3_checked, root7Node160Step1Chunk3_4_checked, root7Node160Step1Chunk3_5_checked, root7Node160Step1Chunk4_0_checked, root7Node160Step1Chunk4_1_checked, root7Node160Step1Chunk4_2_checked, root7Node160Step1Chunk4_3_checked, root7Node160Step1Chunk4_4_checked, root7Node160Step1Chunk4_5_checked, root7Node160Step1Chunk5_0_checked, root7Node160Step1Chunk5_1_checked, root7Node160Step1Chunk5_2_checked, root7Node160Step1Chunk5_3_checked, root7Node160Step1Chunk5_4_checked, root7Node160Step1Chunk5_5_checked, root7Node160Step1Chunk6_0_checked, root7Node160Step1Chunk6_1_checked, root7Node160Step1Chunk6_2_checked, root7Node160Step1Chunk6_3_checked, root7Node160Step1Chunk6_4_checked, root7Node160Step1Chunk6_5_checked, root7Node160Step1Chunk7_0_checked, root7Node160Step1Chunk7_1_checked, root7Node160Step1Chunk7_2_checked, root7Node160Step1Chunk7_3_checked, root7Node160Step1Chunk7_4_checked, root7Node160Step1Chunk7_5_checked, root7Node160Step1Chunk8_0_checked, root7Node160Step1Chunk8_1_checked, root7Node160Step1Chunk8_2_checked, root7Node160Step1Chunk8_3_checked, root7Node160Step1Chunk8_4_checked, root7Node160Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node160Step1_checked :
    checkReplacement table54 root7Node160Domains0 root7Node160Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node160Domains0 root7Node160Domains1
    root7Node160Domains0Fast root7Node160Domains1Fast
    root7Node160Domains0_fast_eq root7Node160Domains1_fast_eq
    root7Node160Step1Narrowing_checked (by decide)
theorem root7Node160Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node160Domains1 (.output 78) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
