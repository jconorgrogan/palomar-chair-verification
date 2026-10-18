module

public import SpectreFinite.RadiusFiveRoot6Part41
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node101Domains0 : Domains 91 State := restrict root6Node95Domains1 30 (8,4)
def root6Node101Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3)]
  | 9 => some [(8,2)]
  | 10 => some [(8,0)]
  | 11 => some [(7,3)]
  | 12 => some [(4,2)]
  | 13 => some [(1,1)]
  | 14 => some [(8,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(6,4)]
  | 19 => some [(1,2)]
  | 20 => some [(7,4)]
  | 21 => some [(8,0)]
  | 22 => some [(8,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(4,3)]
  | 26 => some [(3,5)]
  | 27 => some [(0,3)]
  | 28 => some [(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(8,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,4)]
  | 37 => some [(1,3)]
  | 38 => some [(5,2)]
  | 39 => some [(8,0)]
  | 40 => some [(4,3),(7,1)]
  | 41 => some [(7,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,4)]
  | 50 => some [(1,4),(6,4)]
  | 51 => some [(1,3),(7,3)]
  | 52 => some [(8,2)]
  | 53 => some [(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(4,3)]
  | 60 => some [(7,5)]
  | 61 => some [(0,4),(6,2)]
  | 62 => some [(5,4),(8,4)]
  | 63 => some [(6,4)]
  | 64 => some [(1,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3)]
  | 70 => some [(4,3),(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(0,3)]
  | 73 => some [(8,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(8,1)]
  | 77 => some [(6,5)]
  | 78 => some [(1,3),(7,3)]
  | 79 => some [(4,2)]
  | 80 => some [(5,3)]
  | 81 => some [(5,5),(8,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(0,4),(6,2)]
  | 86 => some [(1,4),(3,4),(7,4)]
  | 87 => some [(0,5),(6,3)]
  | 88 => some [(4,4),(7,2)]
  | 89 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root6Node101Domains0_fast_eq : root6Node101Domains0 = expandDomains root6Node101Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node101Domains0 v = expandDomains root6Node101Domains0Fast v from by decide) v
def root6Node101Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,1)]
  | 5 => [(7,5)]
  | 6 => [(7,2)]
  | 7 => [(7,4)]
  | 8 => [(1,3)]
  | 9 => [(8,2)]
  | 10 => [(8,0)]
  | 11 => [(7,3)]
  | 12 => [(4,2)]
  | 13 => [(1,1)]
  | 14 => [(8,1)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(6,4)]
  | 19 => [(1,2)]
  | 20 => [(7,4)]
  | 21 => [(8,0)]
  | 22 => [(8,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(4,3)]
  | 26 => [(3,5)]
  | 27 => [(0,3)]
  | 28 => [(4,1)]
  | 29 => [(0,2)]
  | 30 => [(8,4)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,4)]
  | 37 => [(1,3)]
  | 38 => [(5,2)]
  | 39 => [(8,0)]
  | 40 => [(7,1)]
  | 41 => [(7,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(6,5)]
  | 48 => [(0,4)]
  | 49 => [(5,4)]
  | 50 => [(1,4),(6,4)]
  | 51 => [(7,3)]
  | 52 => [(8,2)]
  | 53 => [(8,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(7,0)]
  | 59 => [(4,3)]
  | 60 => [(7,5)]
  | 61 => [(6,2)]
  | 62 => [(8,4)]
  | 63 => [(6,4)]
  | 64 => [(1,2)]
  | 65 => [(8,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(7,4)]
  | 69 => [(1,3)]
  | 70 => [(7,1)]
  | 71 => [(7,5)]
  | 72 => [(0,3)]
  | 73 => [(8,1)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(8,1)]
  | 77 => [(6,5)]
  | 78 => [(7,3)]
  | 79 => [(4,2)]
  | 80 => [(5,3)]
  | 81 => [(8,5)]
  | 82 => [(7,0)]
  | 83 => [(8,3)]
  | 84 => [(5,5),(8,5)]
  | 85 => [(6,2)]
  | 86 => [(7,4)]
  | 87 => [(6,3)]
  | 88 => [(7,2)]
  | 89 => [(1,4),(7,4)]
  | _ => [(0,5),(6,3)]
def root6Node101Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3)]
  | 9 => some [(8,2)]
  | 10 => some [(8,0)]
  | 11 => some [(7,3)]
  | 12 => some [(4,2)]
  | 13 => some [(1,1)]
  | 14 => some [(8,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(6,4)]
  | 19 => some [(1,2)]
  | 20 => some [(7,4)]
  | 21 => some [(8,0)]
  | 22 => some [(8,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(4,3)]
  | 26 => some [(3,5)]
  | 27 => some [(0,3)]
  | 28 => some [(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(8,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,4)]
  | 37 => some [(1,3)]
  | 38 => some [(5,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,1)]
  | 41 => some [(7,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,4)]
  | 50 => some [(1,4),(6,4)]
  | 51 => some [(7,3)]
  | 52 => some [(8,2)]
  | 53 => some [(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(4,3)]
  | 60 => some [(7,5)]
  | 61 => some [(6,2)]
  | 62 => some [(8,4)]
  | 63 => some [(6,4)]
  | 64 => some [(1,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3)]
  | 70 => some [(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(0,3)]
  | 73 => some [(8,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(8,1)]
  | 77 => some [(6,5)]
  | 78 => some [(7,3)]
  | 79 => some [(4,2)]
  | 80 => some [(5,3)]
  | 81 => some [(8,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(6,2)]
  | 86 => some [(7,4)]
  | 87 => some [(6,3)]
  | 88 => some [(7,2)]
  | 89 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root6Node101Domains1_fast_eq : root6Node101Domains1 = expandDomains root6Node101Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node101Domains1 v = expandDomains root6Node101Domains1Fast v from by decide) v
theorem root6Node101Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq (by decide)
theorem root6Node101Step1Narrowing_checked :
    checkNarrowing table54 root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root6Node101Domains0 root6Node101Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node101Step1Chunk0_0_checked, root6Node101Step1Chunk0_1_checked, root6Node101Step1Chunk0_2_checked, root6Node101Step1Chunk0_3_checked, root6Node101Step1Chunk0_4_checked, root6Node101Step1Chunk0_5_checked, root6Node101Step1Chunk1_0_checked, root6Node101Step1Chunk1_1_checked, root6Node101Step1Chunk1_2_checked, root6Node101Step1Chunk1_3_checked, root6Node101Step1Chunk1_4_checked, root6Node101Step1Chunk1_5_checked, root6Node101Step1Chunk2_0_checked, root6Node101Step1Chunk2_1_checked, root6Node101Step1Chunk2_2_checked, root6Node101Step1Chunk2_3_checked, root6Node101Step1Chunk2_4_checked, root6Node101Step1Chunk2_5_checked, root6Node101Step1Chunk3_0_checked, root6Node101Step1Chunk3_1_checked, root6Node101Step1Chunk3_2_checked, root6Node101Step1Chunk3_3_checked, root6Node101Step1Chunk3_4_checked, root6Node101Step1Chunk3_5_checked, root6Node101Step1Chunk4_0_checked, root6Node101Step1Chunk4_1_checked, root6Node101Step1Chunk4_2_checked, root6Node101Step1Chunk4_3_checked, root6Node101Step1Chunk4_4_checked, root6Node101Step1Chunk4_5_checked, root6Node101Step1Chunk5_0_checked, root6Node101Step1Chunk5_1_checked, root6Node101Step1Chunk5_2_checked, root6Node101Step1Chunk5_3_checked, root6Node101Step1Chunk5_4_checked, root6Node101Step1Chunk5_5_checked, root6Node101Step1Chunk6_0_checked, root6Node101Step1Chunk6_1_checked, root6Node101Step1Chunk6_2_checked, root6Node101Step1Chunk6_3_checked, root6Node101Step1Chunk6_4_checked, root6Node101Step1Chunk6_5_checked, root6Node101Step1Chunk7_0_checked, root6Node101Step1Chunk7_1_checked, root6Node101Step1Chunk7_2_checked, root6Node101Step1Chunk7_3_checked, root6Node101Step1Chunk7_4_checked, root6Node101Step1Chunk7_5_checked, root6Node101Step1Chunk8_0_checked, root6Node101Step1Chunk8_1_checked, root6Node101Step1Chunk8_2_checked, root6Node101Step1Chunk8_3_checked, root6Node101Step1Chunk8_4_checked, root6Node101Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node101Step1_checked :
    checkReplacement table54 root6Node101Domains0 root6Node101Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node101Domains0 root6Node101Domains1
    root6Node101Domains0Fast root6Node101Domains1Fast
    root6Node101Domains0_fast_eq root6Node101Domains1_fast_eq
    root6Node101Step1Narrowing_checked (by decide)
def root6Node101Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,1)]
  | 5 => [(7,5)]
  | 6 => [(7,2)]
  | 7 => [(7,4)]
  | 8 => [(1,3)]
  | 9 => [(8,2)]
  | 10 => [(8,0)]
  | 11 => [(7,3)]
  | 12 => [(4,2)]
  | 13 => [(1,1)]
  | 14 => [(8,1)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(6,4)]
  | 19 => [(1,2)]
  | 20 => [(7,4)]
  | 21 => [(8,0)]
  | 22 => [(8,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(4,3)]
  | 26 => [(3,5)]
  | 27 => [(0,3)]
  | 28 => [(4,1)]
  | 29 => [(0,2)]
  | 30 => [(8,4)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,4)]
  | 37 => [(1,3)]
  | 38 => [(5,2)]
  | 39 => [(8,0)]
  | 40 => [(7,1)]
  | 41 => [(7,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(6,5)]
  | 48 => [(0,4)]
  | 49 => [(5,4)]
  | 50 => [(1,4)]
  | 51 => [(7,3)]
  | 52 => [(8,2)]
  | 53 => [(8,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(7,0)]
  | 59 => [(4,3)]
  | 60 => [(7,5)]
  | 61 => [(6,2)]
  | 62 => [(8,4)]
  | 63 => [(6,4)]
  | 64 => [(1,2)]
  | 65 => [(8,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(7,4)]
  | 69 => [(1,3)]
  | 70 => [(7,1)]
  | 71 => [(7,5)]
  | 72 => [(0,3)]
  | 73 => [(8,1)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(8,1)]
  | 77 => [(6,5)]
  | 78 => [(7,3)]
  | 79 => [(4,2)]
  | 80 => [(5,3)]
  | 81 => [(8,5)]
  | 82 => [(7,0)]
  | 83 => [(8,3)]
  | 84 => [(8,5)]
  | 85 => [(6,2)]
  | 86 => [(7,4)]
  | 87 => [(6,3)]
  | 88 => [(7,2)]
  | 89 => [(7,4)]
  | _ => [(6,3)]
def root6Node101Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3)]
  | 9 => some [(8,2)]
  | 10 => some [(8,0)]
  | 11 => some [(7,3)]
  | 12 => some [(4,2)]
  | 13 => some [(1,1)]
  | 14 => some [(8,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(6,4)]
  | 19 => some [(1,2)]
  | 20 => some [(7,4)]
  | 21 => some [(8,0)]
  | 22 => some [(8,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(4,3)]
  | 26 => some [(3,5)]
  | 27 => some [(0,3)]
  | 28 => some [(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(8,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,4)]
  | 37 => some [(1,3)]
  | 38 => some [(5,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,1)]
  | 41 => some [(7,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,4)]
  | 50 => some [(1,4)]
  | 51 => some [(7,3)]
  | 52 => some [(8,2)]
  | 53 => some [(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(4,3)]
  | 60 => some [(7,5)]
  | 61 => some [(6,2)]
  | 62 => some [(8,4)]
  | 63 => some [(6,4)]
  | 64 => some [(1,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3)]
  | 70 => some [(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(0,3)]
  | 73 => some [(8,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(8,1)]
  | 77 => some [(6,5)]
  | 78 => some [(7,3)]
  | 79 => some [(4,2)]
  | 80 => some [(5,3)]
  | 81 => some [(8,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(8,5)]
  | 85 => some [(6,2)]
  | 86 => some [(7,4)]
  | 87 => some [(6,3)]
  | 88 => some [(7,2)]
  | 89 => some [(7,4)]
  | _ => some [(6,3)]
theorem root6Node101Domains2_fast_eq : root6Node101Domains2 = expandDomains root6Node101Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node101Domains2 v = expandDomains root6Node101Domains2Fast v from by decide) v
theorem root6Node101Step2Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq (by decide)
theorem root6Node101Step2Narrowing_checked :
    checkNarrowing table57 root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root6Node101Domains1 root6Node101Domains2 (by
      simp only [List.all_cons, List.all_nil, root6Node101Step2Chunk0_0_checked, root6Node101Step2Chunk0_1_checked, root6Node101Step2Chunk0_2_checked, root6Node101Step2Chunk0_3_checked, root6Node101Step2Chunk0_4_checked, root6Node101Step2Chunk0_5_checked, root6Node101Step2Chunk1_0_checked, root6Node101Step2Chunk1_1_checked, root6Node101Step2Chunk1_2_checked, root6Node101Step2Chunk1_3_checked, root6Node101Step2Chunk1_4_checked, root6Node101Step2Chunk1_5_checked, root6Node101Step2Chunk2_0_checked, root6Node101Step2Chunk2_1_checked, root6Node101Step2Chunk2_2_checked, root6Node101Step2Chunk2_3_checked, root6Node101Step2Chunk2_4_checked, root6Node101Step2Chunk2_5_checked, root6Node101Step2Chunk3_0_checked, root6Node101Step2Chunk3_1_checked, root6Node101Step2Chunk3_2_checked, root6Node101Step2Chunk3_3_checked, root6Node101Step2Chunk3_4_checked, root6Node101Step2Chunk3_5_checked, root6Node101Step2Chunk4_0_checked, root6Node101Step2Chunk4_1_checked, root6Node101Step2Chunk4_2_checked, root6Node101Step2Chunk4_3_checked, root6Node101Step2Chunk4_4_checked, root6Node101Step2Chunk4_5_checked, root6Node101Step2Chunk5_0_checked, root6Node101Step2Chunk5_1_checked, root6Node101Step2Chunk5_2_checked, root6Node101Step2Chunk5_3_checked, root6Node101Step2Chunk5_4_checked, root6Node101Step2Chunk5_5_checked, root6Node101Step2Chunk6_0_checked, root6Node101Step2Chunk6_1_checked, root6Node101Step2Chunk6_2_checked, root6Node101Step2Chunk6_3_checked, root6Node101Step2Chunk6_4_checked, root6Node101Step2Chunk6_5_checked, root6Node101Step2Chunk7_0_checked, root6Node101Step2Chunk7_1_checked, root6Node101Step2Chunk7_2_checked, root6Node101Step2Chunk7_3_checked, root6Node101Step2Chunk7_4_checked, root6Node101Step2Chunk7_5_checked, root6Node101Step2Chunk8_0_checked, root6Node101Step2Chunk8_1_checked, root6Node101Step2Chunk8_2_checked, root6Node101Step2Chunk8_3_checked, root6Node101Step2Chunk8_4_checked, root6Node101Step2Chunk8_5_checked, Bool.true_and])
theorem root6Node101Step2_checked :
    checkReplacement table57 root6Node101Domains1 root6Node101Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root6Node101Domains1 root6Node101Domains2
    root6Node101Domains1Fast root6Node101Domains2Fast
    root6Node101Domains1_fast_eq root6Node101Domains2_fast_eq
    root6Node101Step2Narrowing_checked (by decide)
theorem root6Node101Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node101Domains2 (.output 49) = true := by decide
def root6Node102Domains0 : Domains 91 State := restrict root6Node94Domains3 13 (6,1)
def root6Node102Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3)]
  | 9 => some [(8,2)]
  | 10 => some [(8,0)]
  | 11 => some [(7,3)]
  | 12 => some [(4,2)]
  | 13 => some [(6,1)]
  | 14 => some [(8,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(6,4)]
  | 19 => some [(1,2)]
  | 20 => some [(7,4)]
  | 21 => some [(7,0),(8,0)]
  | 22 => some [(8,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(4,3)]
  | 26 => some [(3,5)]
  | 27 => some [(0,3)]
  | 28 => some [(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(4,4),(5,4),(8,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,4)]
  | 37 => some [(1,3)]
  | 38 => some [(5,2)]
  | 39 => some [(8,0)]
  | 40 => some [(4,3),(7,1)]
  | 41 => some [(7,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,4)]
  | 50 => some [(1,4),(6,4)]
  | 51 => some [(1,3),(7,3)]
  | 52 => some [(8,2)]
  | 53 => some [(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(4,3)]
  | 60 => some [(7,5)]
  | 61 => some [(0,4),(6,2)]
  | 62 => some [(5,4),(8,4)]
  | 63 => some [(6,4)]
  | 64 => some [(1,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3)]
  | 70 => some [(4,3),(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(0,3)]
  | 73 => some [(8,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(8,1)]
  | 77 => some [(6,5)]
  | 78 => some [(1,3),(7,3)]
  | 79 => some [(4,2)]
  | 80 => some [(5,3)]
  | 81 => some [(5,5),(8,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(0,4),(6,2)]
  | 86 => some [(1,4),(3,4),(7,4)]
  | 87 => some [(0,5),(6,3)]
  | 88 => some [(4,4),(7,2)]
  | 89 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root6Node102Domains0_fast_eq : root6Node102Domains0 = expandDomains root6Node102Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node102Domains0 v = expandDomains root6Node102Domains0Fast v from by decide) v
def root6Node102Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,1)]
  | 5 => [(7,5)]
  | 6 => [(7,2)]
  | 7 => [(7,4)]
  | 8 => [(1,3)]
  | 9 => [(8,2)]
  | 10 => [(8,0)]
  | 11 => [(7,3)]
  | 12 => [(4,2)]
  | 13 => [(6,1)]
  | 14 => [(8,1)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(6,4)]
  | 19 => [(1,2)]
  | 20 => [(7,4)]
  | 21 => [(7,0)]
  | 22 => [(8,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(4,3)]
  | 26 => [(3,5)]
  | 27 => [(0,3)]
  | 28 => [(4,1)]
  | 29 => [(0,2)]
  | 30 => [(4,4)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,4)]
  | 37 => [(1,3)]
  | 38 => [(5,2)]
  | 39 => [(8,0)]
  | 40 => [(7,1)]
  | 41 => [(7,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(6,5)]
  | 48 => [(0,4)]
  | 49 => [(5,4)]
  | 50 => [(1,4),(6,4)]
  | 51 => [(7,3)]
  | 52 => [(8,2)]
  | 53 => [(8,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(7,0)]
  | 59 => [(4,3)]
  | 60 => [(7,5)]
  | 61 => [(6,2)]
  | 62 => [(8,4)]
  | 63 => [(6,4)]
  | 64 => [(1,2)]
  | 65 => [(8,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(7,4)]
  | 69 => [(1,3)]
  | 70 => [(7,1)]
  | 71 => [(7,5)]
  | 72 => [(0,3)]
  | 73 => [(8,1)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(8,1)]
  | 77 => [(6,5)]
  | 78 => [(7,3)]
  | 79 => [(4,2)]
  | 80 => [(5,3)]
  | 81 => [(8,5)]
  | 82 => [(7,0)]
  | 83 => [(8,3)]
  | 84 => [(5,5),(8,5)]
  | 85 => [(6,2)]
  | 86 => [(7,4)]
  | 87 => [(6,3)]
  | 88 => [(7,2)]
  | 89 => [(1,4),(7,4)]
  | _ => [(0,5),(6,3)]
def root6Node102Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3)]
  | 9 => some [(8,2)]
  | 10 => some [(8,0)]
  | 11 => some [(7,3)]
  | 12 => some [(4,2)]
  | 13 => some [(6,1)]
  | 14 => some [(8,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(6,4)]
  | 19 => some [(1,2)]
  | 20 => some [(7,4)]
  | 21 => some [(7,0)]
  | 22 => some [(8,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(4,3)]
  | 26 => some [(3,5)]
  | 27 => some [(0,3)]
  | 28 => some [(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(4,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,4)]
  | 37 => some [(1,3)]
  | 38 => some [(5,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,1)]
  | 41 => some [(7,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,4)]
  | 50 => some [(1,4),(6,4)]
  | 51 => some [(7,3)]
  | 52 => some [(8,2)]
  | 53 => some [(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(4,3)]
  | 60 => some [(7,5)]
  | 61 => some [(6,2)]
  | 62 => some [(8,4)]
  | 63 => some [(6,4)]
  | 64 => some [(1,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3)]
  | 70 => some [(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(0,3)]
  | 73 => some [(8,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(8,1)]
  | 77 => some [(6,5)]
  | 78 => some [(7,3)]
  | 79 => some [(4,2)]
  | 80 => some [(5,3)]
  | 81 => some [(8,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(6,2)]
  | 86 => some [(7,4)]
  | 87 => some [(6,3)]
  | 88 => some [(7,2)]
  | 89 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root6Node102Domains1_fast_eq : root6Node102Domains1 = expandDomains root6Node102Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node102Domains1 v = expandDomains root6Node102Domains1Fast v from by decide) v
theorem root6Node102Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq (by decide)
theorem root6Node102Step1Narrowing_checked :
    checkNarrowing table54 root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root6Node102Domains0 root6Node102Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node102Step1Chunk0_0_checked, root6Node102Step1Chunk0_1_checked, root6Node102Step1Chunk0_2_checked, root6Node102Step1Chunk0_3_checked, root6Node102Step1Chunk0_4_checked, root6Node102Step1Chunk0_5_checked, root6Node102Step1Chunk1_0_checked, root6Node102Step1Chunk1_1_checked, root6Node102Step1Chunk1_2_checked, root6Node102Step1Chunk1_3_checked, root6Node102Step1Chunk1_4_checked, root6Node102Step1Chunk1_5_checked, root6Node102Step1Chunk2_0_checked, root6Node102Step1Chunk2_1_checked, root6Node102Step1Chunk2_2_checked, root6Node102Step1Chunk2_3_checked, root6Node102Step1Chunk2_4_checked, root6Node102Step1Chunk2_5_checked, root6Node102Step1Chunk3_0_checked, root6Node102Step1Chunk3_1_checked, root6Node102Step1Chunk3_2_checked, root6Node102Step1Chunk3_3_checked, root6Node102Step1Chunk3_4_checked, root6Node102Step1Chunk3_5_checked, root6Node102Step1Chunk4_0_checked, root6Node102Step1Chunk4_1_checked, root6Node102Step1Chunk4_2_checked, root6Node102Step1Chunk4_3_checked, root6Node102Step1Chunk4_4_checked, root6Node102Step1Chunk4_5_checked, root6Node102Step1Chunk5_0_checked, root6Node102Step1Chunk5_1_checked, root6Node102Step1Chunk5_2_checked, root6Node102Step1Chunk5_3_checked, root6Node102Step1Chunk5_4_checked, root6Node102Step1Chunk5_5_checked, root6Node102Step1Chunk6_0_checked, root6Node102Step1Chunk6_1_checked, root6Node102Step1Chunk6_2_checked, root6Node102Step1Chunk6_3_checked, root6Node102Step1Chunk6_4_checked, root6Node102Step1Chunk6_5_checked, root6Node102Step1Chunk7_0_checked, root6Node102Step1Chunk7_1_checked, root6Node102Step1Chunk7_2_checked, root6Node102Step1Chunk7_3_checked, root6Node102Step1Chunk7_4_checked, root6Node102Step1Chunk7_5_checked, root6Node102Step1Chunk8_0_checked, root6Node102Step1Chunk8_1_checked, root6Node102Step1Chunk8_2_checked, root6Node102Step1Chunk8_3_checked, root6Node102Step1Chunk8_4_checked, root6Node102Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node102Step1_checked :
    checkReplacement table54 root6Node102Domains0 root6Node102Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node102Domains0 root6Node102Domains1
    root6Node102Domains0Fast root6Node102Domains1Fast
    root6Node102Domains0_fast_eq root6Node102Domains1_fast_eq
    root6Node102Step1Narrowing_checked (by decide)
def root6Node102Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,1)]
  | 5 => [(7,5)]
  | 6 => [(7,2)]
  | 7 => [(7,4)]
  | 8 => [(1,3)]
  | 9 => [(8,2)]
  | 10 => [(8,0)]
  | 11 => [(7,3)]
  | 12 => [(4,2)]
  | 13 => [(6,1)]
  | 14 => [(8,1)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(6,4)]
  | 19 => [(1,2)]
  | 20 => [(7,4)]
  | 21 => [(7,0)]
  | 22 => [(8,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(4,3)]
  | 26 => [(3,5)]
  | 27 => [(0,3)]
  | 28 => [(4,1)]
  | 29 => [(0,2)]
  | 30 => [(4,4)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,4)]
  | 37 => [(1,3)]
  | 38 => [(5,2)]
  | 39 => [(8,0)]
  | 40 => [(7,1)]
  | 41 => [(7,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(6,5)]
  | 48 => [(0,4)]
  | 49 => [(5,4)]
  | 50 => [(1,4)]
  | 51 => [(7,3)]
  | 52 => [(8,2)]
  | 53 => [(8,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(7,0)]
  | 59 => [(4,3)]
  | 60 => [(7,5)]
  | 61 => [(6,2)]
  | 62 => [(8,4)]
  | 63 => [(6,4)]
  | 64 => [(1,2)]
  | 65 => [(8,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(7,4)]
  | 69 => [(1,3)]
  | 70 => [(7,1)]
  | 71 => [(7,5)]
  | 72 => [(0,3)]
  | 73 => [(8,1)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(8,1)]
  | 77 => [(6,5)]
  | 78 => [(7,3)]
  | 79 => [(4,2)]
  | 80 => [(5,3)]
  | 81 => [(8,5)]
  | 82 => [(7,0)]
  | 83 => [(8,3)]
  | 84 => [(8,5)]
  | 85 => [(6,2)]
  | 86 => [(7,4)]
  | 87 => [(6,3)]
  | 88 => [(7,2)]
  | 89 => [(7,4)]
  | _ => [(6,3)]
def root6Node102Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3)]
  | 9 => some [(8,2)]
  | 10 => some [(8,0)]
  | 11 => some [(7,3)]
  | 12 => some [(4,2)]
  | 13 => some [(6,1)]
  | 14 => some [(8,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(6,4)]
  | 19 => some [(1,2)]
  | 20 => some [(7,4)]
  | 21 => some [(7,0)]
  | 22 => some [(8,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(4,3)]
  | 26 => some [(3,5)]
  | 27 => some [(0,3)]
  | 28 => some [(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(4,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,4)]
  | 37 => some [(1,3)]
  | 38 => some [(5,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,1)]
  | 41 => some [(7,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,4)]
  | 50 => some [(1,4)]
  | 51 => some [(7,3)]
  | 52 => some [(8,2)]
  | 53 => some [(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(4,3)]
  | 60 => some [(7,5)]
  | 61 => some [(6,2)]
  | 62 => some [(8,4)]
  | 63 => some [(6,4)]
  | 64 => some [(1,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3)]
  | 70 => some [(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(0,3)]
  | 73 => some [(8,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(8,1)]
  | 77 => some [(6,5)]
  | 78 => some [(7,3)]
  | 79 => some [(4,2)]
  | 80 => some [(5,3)]
  | 81 => some [(8,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(8,5)]
  | 85 => some [(6,2)]
  | 86 => some [(7,4)]
  | 87 => some [(6,3)]
  | 88 => some [(7,2)]
  | 89 => some [(7,4)]
  | _ => some [(6,3)]
theorem root6Node102Domains2_fast_eq : root6Node102Domains2 = expandDomains root6Node102Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node102Domains2 v = expandDomains root6Node102Domains2Fast v from by decide) v
theorem root6Node102Step2Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq (by decide)
theorem root6Node102Step2Narrowing_checked :
    checkNarrowing table57 root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root6Node102Domains1 root6Node102Domains2 (by
      simp only [List.all_cons, List.all_nil, root6Node102Step2Chunk0_0_checked, root6Node102Step2Chunk0_1_checked, root6Node102Step2Chunk0_2_checked, root6Node102Step2Chunk0_3_checked, root6Node102Step2Chunk0_4_checked, root6Node102Step2Chunk0_5_checked, root6Node102Step2Chunk1_0_checked, root6Node102Step2Chunk1_1_checked, root6Node102Step2Chunk1_2_checked, root6Node102Step2Chunk1_3_checked, root6Node102Step2Chunk1_4_checked, root6Node102Step2Chunk1_5_checked, root6Node102Step2Chunk2_0_checked, root6Node102Step2Chunk2_1_checked, root6Node102Step2Chunk2_2_checked, root6Node102Step2Chunk2_3_checked, root6Node102Step2Chunk2_4_checked, root6Node102Step2Chunk2_5_checked, root6Node102Step2Chunk3_0_checked, root6Node102Step2Chunk3_1_checked, root6Node102Step2Chunk3_2_checked, root6Node102Step2Chunk3_3_checked, root6Node102Step2Chunk3_4_checked, root6Node102Step2Chunk3_5_checked, root6Node102Step2Chunk4_0_checked, root6Node102Step2Chunk4_1_checked, root6Node102Step2Chunk4_2_checked, root6Node102Step2Chunk4_3_checked, root6Node102Step2Chunk4_4_checked, root6Node102Step2Chunk4_5_checked, root6Node102Step2Chunk5_0_checked, root6Node102Step2Chunk5_1_checked, root6Node102Step2Chunk5_2_checked, root6Node102Step2Chunk5_3_checked, root6Node102Step2Chunk5_4_checked, root6Node102Step2Chunk5_5_checked, root6Node102Step2Chunk6_0_checked, root6Node102Step2Chunk6_1_checked, root6Node102Step2Chunk6_2_checked, root6Node102Step2Chunk6_3_checked, root6Node102Step2Chunk6_4_checked, root6Node102Step2Chunk6_5_checked, root6Node102Step2Chunk7_0_checked, root6Node102Step2Chunk7_1_checked, root6Node102Step2Chunk7_2_checked, root6Node102Step2Chunk7_3_checked, root6Node102Step2Chunk7_4_checked, root6Node102Step2Chunk7_5_checked, root6Node102Step2Chunk8_0_checked, root6Node102Step2Chunk8_1_checked, root6Node102Step2Chunk8_2_checked, root6Node102Step2Chunk8_3_checked, root6Node102Step2Chunk8_4_checked, root6Node102Step2Chunk8_5_checked, Bool.true_and])
theorem root6Node102Step2_checked :
    checkReplacement table57 root6Node102Domains1 root6Node102Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root6Node102Domains1 root6Node102Domains2
    root6Node102Domains1Fast root6Node102Domains2Fast
    root6Node102Domains1_fast_eq root6Node102Domains2_fast_eq
    root6Node102Step2Narrowing_checked (by decide)
theorem root6Node102Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node102Domains2 (.output 50) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
