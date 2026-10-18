module

public import SpectreFinite.RadiusFiveRoot8Part30
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable12
public import SpectreFinite.RadiusFiveTable27
public import SpectreFinite.RadiusFiveTable54

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node78Domains0 : Domains 91 State := restrict root8Node74Domains1 70 (6,3)
def root8Node78Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(3,4)]
  | 13 => some [(5,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3)]
  | 20 => some [(0,2)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(4,0)]
  | 30 => some [(2,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(6,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(1,1)]
  | 79 => some [(5,1),(5,4)]
  | 80 => some [(0,1),(6,4)]
  | 81 => some [(1,2),(6,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5),(7,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(2,1),(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root8Node78Domains0_fast_eq : root8Node78Domains0 = expandDomains root8Node78Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node78Domains0 v = expandDomains root8Node78Domains0Fast v from by decide) v
def root8Node78Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,2)]
  | 6 => [(8,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(3,4)]
  | 13 => [(5,3)]
  | 14 => [(5,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(2,3)]
  | 20 => [(0,2)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(4,0)]
  | 30 => [(2,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(4,0)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0)]
  | 51 => [(6,1)]
  | 52 => [(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4)]
  | 59 => [(1,3)]
  | 60 => [(8,2)]
  | 61 => [(8,3)]
  | 62 => [(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(8,1)]
  | 68 => [(6,5)]
  | 69 => [(0,4)]
  | 70 => [(6,3)]
  | 71 => [(7,2)]
  | 72 => [(4,0)]
  | 73 => [(7,3)]
  | 74 => [(4,2)]
  | 75 => [(5,3)]
  | 76 => [(8,5)]
  | 77 => [(7,0)]
  | 78 => [(1,1)]
  | 79 => [(5,1)]
  | 80 => [(0,1)]
  | 81 => [(6,2)]
  | 82 => [(7,4)]
  | 83 => [(6,3)]
  | 84 => [(7,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5)]
  | 87 => [(1,0)]
  | 88 => [(2,1)]
  | 89 => [(0,2)]
  | _ => [(1,1)]
def root8Node78Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(3,4)]
  | 13 => some [(5,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3)]
  | 20 => some [(0,2)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(4,0)]
  | 30 => some [(2,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(4,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(1,1)]
  | 79 => some [(5,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(1,0)]
  | 88 => some [(2,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root8Node78Domains1_fast_eq : root8Node78Domains1 = expandDomains root8Node78Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node78Domains1 v = expandDomains root8Node78Domains1Fast v from by decide) v
theorem root8Node78Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq (by decide)
theorem root8Node78Step1Narrowing_checked :
    checkNarrowing table54 root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root8Node78Domains0 root8Node78Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node78Step1Chunk0_0_checked, root8Node78Step1Chunk0_1_checked, root8Node78Step1Chunk0_2_checked, root8Node78Step1Chunk0_3_checked, root8Node78Step1Chunk0_4_checked, root8Node78Step1Chunk0_5_checked, root8Node78Step1Chunk1_0_checked, root8Node78Step1Chunk1_1_checked, root8Node78Step1Chunk1_2_checked, root8Node78Step1Chunk1_3_checked, root8Node78Step1Chunk1_4_checked, root8Node78Step1Chunk1_5_checked, root8Node78Step1Chunk2_0_checked, root8Node78Step1Chunk2_1_checked, root8Node78Step1Chunk2_2_checked, root8Node78Step1Chunk2_3_checked, root8Node78Step1Chunk2_4_checked, root8Node78Step1Chunk2_5_checked, root8Node78Step1Chunk3_0_checked, root8Node78Step1Chunk3_1_checked, root8Node78Step1Chunk3_2_checked, root8Node78Step1Chunk3_3_checked, root8Node78Step1Chunk3_4_checked, root8Node78Step1Chunk3_5_checked, root8Node78Step1Chunk4_0_checked, root8Node78Step1Chunk4_1_checked, root8Node78Step1Chunk4_2_checked, root8Node78Step1Chunk4_3_checked, root8Node78Step1Chunk4_4_checked, root8Node78Step1Chunk4_5_checked, root8Node78Step1Chunk5_0_checked, root8Node78Step1Chunk5_1_checked, root8Node78Step1Chunk5_2_checked, root8Node78Step1Chunk5_3_checked, root8Node78Step1Chunk5_4_checked, root8Node78Step1Chunk5_5_checked, root8Node78Step1Chunk6_0_checked, root8Node78Step1Chunk6_1_checked, root8Node78Step1Chunk6_2_checked, root8Node78Step1Chunk6_3_checked, root8Node78Step1Chunk6_4_checked, root8Node78Step1Chunk6_5_checked, root8Node78Step1Chunk7_0_checked, root8Node78Step1Chunk7_1_checked, root8Node78Step1Chunk7_2_checked, root8Node78Step1Chunk7_3_checked, root8Node78Step1Chunk7_4_checked, root8Node78Step1Chunk7_5_checked, root8Node78Step1Chunk8_0_checked, root8Node78Step1Chunk8_1_checked, root8Node78Step1Chunk8_2_checked, root8Node78Step1Chunk8_3_checked, root8Node78Step1Chunk8_4_checked, root8Node78Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node78Step1_checked :
    checkReplacement table54 root8Node78Domains0 root8Node78Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node78Domains0 root8Node78Domains1
    root8Node78Domains0Fast root8Node78Domains1Fast
    root8Node78Domains0_fast_eq root8Node78Domains1_fast_eq
    root8Node78Step1Narrowing_checked (by decide)
theorem root8Node78Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node78Domains1 (.output 38) = true := by decide
def root8Node79Domains0 : Domains 91 State := restrict root8Node73Domains4 5 (8,2)
def root8Node79Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(3,4),(5,4)]
  | 13 => some [(5,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3),(4,3)]
  | 20 => some [(0,2),(1,5),(3,5)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(2,0),(2,4),(4,0)]
  | 30 => some [(2,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(3,1),(5,1),(7,1)]
  | 39 => some [(0,1),(6,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3)]
  | 49 => some [(4,5),(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(1,3)]
  | 60 => some [(7,2),(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5),(6,5)]
  | 69 => some [(0,4),(6,1)]
  | 70 => some [(1,3),(6,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(1,1)]
  | 79 => some [(5,1),(5,4)]
  | 80 => some [(0,1),(6,4)]
  | 81 => some [(1,2),(6,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5),(7,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(2,1),(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root8Node79Domains0_fast_eq : root8Node79Domains0 = expandDomains root8Node79Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node79Domains0 v = expandDomains root8Node79Domains0Fast v from by decide) v
def root8Node79Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(8,2)]
  | 6 => [(8,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(5,3)]
  | 14 => [(5,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(1,5),(3,5)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(2,0),(2,4)]
  | 30 => [(2,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(3,1),(7,1)]
  | 39 => [(0,1),(6,5)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(4,0)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(1,0),(7,0)]
  | 51 => [(6,1)]
  | 52 => [(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(8,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(1,3),(6,3)]
  | 71 => [(7,2),(8,2)]
  | 72 => [(4,0),(8,0)]
  | 73 => [(7,3)]
  | 74 => [(4,2)]
  | 75 => [(5,3)]
  | 76 => [(8,5)]
  | 77 => [(7,0)]
  | 78 => [(0,4),(1,1)]
  | 79 => [(5,1),(5,4)]
  | 80 => [(0,1),(6,4)]
  | 81 => [(1,2),(6,2)]
  | 82 => [(7,4)]
  | 83 => [(6,3)]
  | 84 => [(7,2)]
  | 85 => [(4,3),(8,3)]
  | 86 => [(3,5),(5,5),(7,5)]
  | 87 => [(0,3),(1,0)]
  | 88 => [(2,1),(4,1)]
  | 89 => [(0,2)]
  | _ => [(1,1)]
def root8Node79Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(5,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5),(3,5)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(2,0),(2,4)]
  | 30 => some [(2,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1),(7,1)]
  | 39 => some [(0,1),(6,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(1,3),(6,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(1,1)]
  | 79 => some [(5,1),(5,4)]
  | 80 => some [(0,1),(6,4)]
  | 81 => some [(1,2),(6,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5),(7,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(2,1),(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root8Node79Domains1_fast_eq : root8Node79Domains1 = expandDomains root8Node79Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node79Domains1 v = expandDomains root8Node79Domains1Fast v from by decide) v
theorem root8Node79Step1Chunk0_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_0⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk0_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_1⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk0_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_2⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk0_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_3⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk0_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_4⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk0_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_5⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk1_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_0⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk1_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_1⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk1_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_2⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk1_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_3⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk1_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_4⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk1_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_5⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk2_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_0⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk2_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_1⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk2_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_2⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk2_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_3⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk2_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_4⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk2_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_5⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk3_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_0⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk3_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_1⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk3_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_2⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk3_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_3⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk3_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_4⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk3_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_5⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk4_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_0⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk4_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_1⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk4_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_2⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk4_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_3⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk4_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_4⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk4_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_5⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk5_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_0⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk5_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_1⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk5_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_2⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk5_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_3⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk5_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_4⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk5_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_5⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk6_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_0⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk6_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_1⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk6_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_2⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk6_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_3⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk6_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_4⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk6_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_5⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk7_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_0⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk7_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_1⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk7_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_2⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk7_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_3⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk7_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_4⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk7_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_5⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk8_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_0⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk8_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_1⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk8_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_2⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk8_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_3⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk8_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_4⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Chunk8_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_5⟩
      root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq (by decide)
theorem root8Node79Step1Narrowing_checked :
    checkNarrowing table27 root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkNarrowing_flatten table27Scope [table27Rows0_0,table27Rows0_1,table27Rows0_2,table27Rows0_3,table27Rows0_4,table27Rows0_5,table27Rows1_0,table27Rows1_1,table27Rows1_2,table27Rows1_3,table27Rows1_4,table27Rows1_5,table27Rows2_0,table27Rows2_1,table27Rows2_2,table27Rows2_3,table27Rows2_4,table27Rows2_5,table27Rows3_0,table27Rows3_1,table27Rows3_2,table27Rows3_3,table27Rows3_4,table27Rows3_5,table27Rows4_0,table27Rows4_1,table27Rows4_2,table27Rows4_3,table27Rows4_4,table27Rows4_5,table27Rows5_0,table27Rows5_1,table27Rows5_2,table27Rows5_3,table27Rows5_4,table27Rows5_5,table27Rows6_0,table27Rows6_1,table27Rows6_2,table27Rows6_3,table27Rows6_4,table27Rows6_5,table27Rows7_0,table27Rows7_1,table27Rows7_2,table27Rows7_3,table27Rows7_4,table27Rows7_5,table27Rows8_0,table27Rows8_1,table27Rows8_2,table27Rows8_3,table27Rows8_4,table27Rows8_5]
    root8Node79Domains0 root8Node79Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node79Step1Chunk0_0_checked, root8Node79Step1Chunk0_1_checked, root8Node79Step1Chunk0_2_checked, root8Node79Step1Chunk0_3_checked, root8Node79Step1Chunk0_4_checked, root8Node79Step1Chunk0_5_checked, root8Node79Step1Chunk1_0_checked, root8Node79Step1Chunk1_1_checked, root8Node79Step1Chunk1_2_checked, root8Node79Step1Chunk1_3_checked, root8Node79Step1Chunk1_4_checked, root8Node79Step1Chunk1_5_checked, root8Node79Step1Chunk2_0_checked, root8Node79Step1Chunk2_1_checked, root8Node79Step1Chunk2_2_checked, root8Node79Step1Chunk2_3_checked, root8Node79Step1Chunk2_4_checked, root8Node79Step1Chunk2_5_checked, root8Node79Step1Chunk3_0_checked, root8Node79Step1Chunk3_1_checked, root8Node79Step1Chunk3_2_checked, root8Node79Step1Chunk3_3_checked, root8Node79Step1Chunk3_4_checked, root8Node79Step1Chunk3_5_checked, root8Node79Step1Chunk4_0_checked, root8Node79Step1Chunk4_1_checked, root8Node79Step1Chunk4_2_checked, root8Node79Step1Chunk4_3_checked, root8Node79Step1Chunk4_4_checked, root8Node79Step1Chunk4_5_checked, root8Node79Step1Chunk5_0_checked, root8Node79Step1Chunk5_1_checked, root8Node79Step1Chunk5_2_checked, root8Node79Step1Chunk5_3_checked, root8Node79Step1Chunk5_4_checked, root8Node79Step1Chunk5_5_checked, root8Node79Step1Chunk6_0_checked, root8Node79Step1Chunk6_1_checked, root8Node79Step1Chunk6_2_checked, root8Node79Step1Chunk6_3_checked, root8Node79Step1Chunk6_4_checked, root8Node79Step1Chunk6_5_checked, root8Node79Step1Chunk7_0_checked, root8Node79Step1Chunk7_1_checked, root8Node79Step1Chunk7_2_checked, root8Node79Step1Chunk7_3_checked, root8Node79Step1Chunk7_4_checked, root8Node79Step1Chunk7_5_checked, root8Node79Step1Chunk8_0_checked, root8Node79Step1Chunk8_1_checked, root8Node79Step1Chunk8_2_checked, root8Node79Step1Chunk8_3_checked, root8Node79Step1Chunk8_4_checked, root8Node79Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node79Step1_checked :
    checkReplacement table27 root8Node79Domains0 root8Node79Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node79Domains0 root8Node79Domains1
    root8Node79Domains0Fast root8Node79Domains1Fast
    root8Node79Domains0_fast_eq root8Node79Domains1_fast_eq
    root8Node79Step1Narrowing_checked (by decide)
def root8Node80Domains0 : Domains 91 State := restrict root8Node79Domains1 20 (1,5)
def root8Node80Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(5,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(2,0),(2,4)]
  | 30 => some [(2,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1),(7,1)]
  | 39 => some [(0,1),(6,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(1,3),(6,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(1,1)]
  | 79 => some [(5,1),(5,4)]
  | 80 => some [(0,1),(6,4)]
  | 81 => some [(1,2),(6,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5),(7,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(2,1),(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root8Node80Domains0_fast_eq : root8Node80Domains0 = expandDomains root8Node80Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node80Domains0 v = expandDomains root8Node80Domains0Fast v from by decide) v
def root8Node80Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(8,2)]
  | 6 => [(8,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(5,3)]
  | 14 => [(5,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(1,5)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(2,0)]
  | 30 => [(2,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(3,1)]
  | 39 => [(0,1)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(4,0)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(1,0)]
  | 51 => [(6,1)]
  | 52 => [(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(8,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(1,3),(6,3)]
  | 71 => [(7,2),(8,2)]
  | 72 => [(4,0),(8,0)]
  | 73 => [(7,3)]
  | 74 => [(4,2)]
  | 75 => [(5,3)]
  | 76 => [(8,5)]
  | 77 => [(7,0)]
  | 78 => [(0,4),(1,1)]
  | 79 => [(5,1),(5,4)]
  | 80 => [(0,1),(6,4)]
  | 81 => [(1,2),(6,2)]
  | 82 => [(7,4)]
  | 83 => [(6,3)]
  | 84 => [(7,2)]
  | 85 => [(4,3),(8,3)]
  | 86 => [(3,5),(5,5),(7,5)]
  | 87 => [(0,3),(1,0)]
  | 88 => [(2,1),(4,1)]
  | 89 => [(0,2)]
  | _ => [(1,1)]
def root8Node80Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(5,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(2,0)]
  | 30 => some [(2,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(1,3),(6,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(1,1)]
  | 79 => some [(5,1),(5,4)]
  | 80 => some [(0,1),(6,4)]
  | 81 => some [(1,2),(6,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5),(7,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(2,1),(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root8Node80Domains1_fast_eq : root8Node80Domains1 = expandDomains root8Node80Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node80Domains1 v = expandDomains root8Node80Domains1Fast v from by decide) v
theorem root8Node80Step1Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq (by decide)
theorem root8Node80Step1Narrowing_checked :
    checkNarrowing table12 root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkNarrowing_flatten table12Scope [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5]
    root8Node80Domains0 root8Node80Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node80Step1Chunk0_0_checked, root8Node80Step1Chunk0_1_checked, root8Node80Step1Chunk0_2_checked, root8Node80Step1Chunk0_3_checked, root8Node80Step1Chunk0_4_checked, root8Node80Step1Chunk0_5_checked, root8Node80Step1Chunk1_0_checked, root8Node80Step1Chunk1_1_checked, root8Node80Step1Chunk1_2_checked, root8Node80Step1Chunk1_3_checked, root8Node80Step1Chunk1_4_checked, root8Node80Step1Chunk1_5_checked, root8Node80Step1Chunk2_0_checked, root8Node80Step1Chunk2_1_checked, root8Node80Step1Chunk2_2_checked, root8Node80Step1Chunk2_3_checked, root8Node80Step1Chunk2_4_checked, root8Node80Step1Chunk2_5_checked, root8Node80Step1Chunk3_0_checked, root8Node80Step1Chunk3_1_checked, root8Node80Step1Chunk3_2_checked, root8Node80Step1Chunk3_3_checked, root8Node80Step1Chunk3_4_checked, root8Node80Step1Chunk3_5_checked, root8Node80Step1Chunk4_0_checked, root8Node80Step1Chunk4_1_checked, root8Node80Step1Chunk4_2_checked, root8Node80Step1Chunk4_3_checked, root8Node80Step1Chunk4_4_checked, root8Node80Step1Chunk4_5_checked, root8Node80Step1Chunk5_0_checked, root8Node80Step1Chunk5_1_checked, root8Node80Step1Chunk5_2_checked, root8Node80Step1Chunk5_3_checked, root8Node80Step1Chunk5_4_checked, root8Node80Step1Chunk5_5_checked, root8Node80Step1Chunk6_0_checked, root8Node80Step1Chunk6_1_checked, root8Node80Step1Chunk6_2_checked, root8Node80Step1Chunk6_3_checked, root8Node80Step1Chunk6_4_checked, root8Node80Step1Chunk6_5_checked, root8Node80Step1Chunk7_0_checked, root8Node80Step1Chunk7_1_checked, root8Node80Step1Chunk7_2_checked, root8Node80Step1Chunk7_3_checked, root8Node80Step1Chunk7_4_checked, root8Node80Step1Chunk7_5_checked, root8Node80Step1Chunk8_0_checked, root8Node80Step1Chunk8_1_checked, root8Node80Step1Chunk8_2_checked, root8Node80Step1Chunk8_3_checked, root8Node80Step1Chunk8_4_checked, root8Node80Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node80Step1_checked :
    checkReplacement table12 root8Node80Domains0 root8Node80Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node80Domains0 root8Node80Domains1
    root8Node80Domains0Fast root8Node80Domains1Fast
    root8Node80Domains0_fast_eq root8Node80Domains1_fast_eq
    root8Node80Step1Narrowing_checked (by decide)
def root8Node81Domains0 : Domains 91 State := restrict root8Node80Domains1 70 (1,3)
def root8Node81Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(5,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(2,0)]
  | 30 => some [(2,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(1,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(1,1)]
  | 79 => some [(5,1),(5,4)]
  | 80 => some [(0,1),(6,4)]
  | 81 => some [(1,2),(6,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5),(7,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(2,1),(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root8Node81Domains0_fast_eq : root8Node81Domains0 = expandDomains root8Node81Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node81Domains0 v = expandDomains root8Node81Domains0Fast v from by decide) v
def root8Node81Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(8,2)]
  | 6 => [(8,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(5,3)]
  | 14 => [(5,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(1,5)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(2,0)]
  | 30 => [(2,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(3,1)]
  | 39 => [(0,1)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(4,0)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(1,0)]
  | 51 => [(6,1)]
  | 52 => [(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(8,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(1,3)]
  | 71 => [(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3)]
  | 74 => [(4,2)]
  | 75 => [(5,3)]
  | 76 => [(8,5)]
  | 77 => [(7,0)]
  | 78 => [(0,4)]
  | 79 => [(5,4)]
  | 80 => [(6,4)]
  | 81 => [(1,2)]
  | 82 => [(7,4)]
  | 83 => [(6,3)]
  | 84 => [(7,2)]
  | 85 => [(4,3)]
  | 86 => [(3,5),(7,5)]
  | 87 => [(0,3)]
  | 88 => [(4,1)]
  | 89 => [(0,2)]
  | _ => [(1,1)]
def root8Node81Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(5,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(1,5)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(2,0)]
  | 30 => some [(2,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(3,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(1,3)]
  | 71 => some [(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4)]
  | 79 => some [(5,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3)]
  | 86 => some [(3,5),(7,5)]
  | 87 => some [(0,3)]
  | 88 => some [(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root8Node81Domains1_fast_eq : root8Node81Domains1 = expandDomains root8Node81Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node81Domains1 v = expandDomains root8Node81Domains1Fast v from by decide) v
theorem root8Node81Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq (by decide)
theorem root8Node81Step1Narrowing_checked :
    checkNarrowing table54 root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root8Node81Domains0 root8Node81Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node81Step1Chunk0_0_checked, root8Node81Step1Chunk0_1_checked, root8Node81Step1Chunk0_2_checked, root8Node81Step1Chunk0_3_checked, root8Node81Step1Chunk0_4_checked, root8Node81Step1Chunk0_5_checked, root8Node81Step1Chunk1_0_checked, root8Node81Step1Chunk1_1_checked, root8Node81Step1Chunk1_2_checked, root8Node81Step1Chunk1_3_checked, root8Node81Step1Chunk1_4_checked, root8Node81Step1Chunk1_5_checked, root8Node81Step1Chunk2_0_checked, root8Node81Step1Chunk2_1_checked, root8Node81Step1Chunk2_2_checked, root8Node81Step1Chunk2_3_checked, root8Node81Step1Chunk2_4_checked, root8Node81Step1Chunk2_5_checked, root8Node81Step1Chunk3_0_checked, root8Node81Step1Chunk3_1_checked, root8Node81Step1Chunk3_2_checked, root8Node81Step1Chunk3_3_checked, root8Node81Step1Chunk3_4_checked, root8Node81Step1Chunk3_5_checked, root8Node81Step1Chunk4_0_checked, root8Node81Step1Chunk4_1_checked, root8Node81Step1Chunk4_2_checked, root8Node81Step1Chunk4_3_checked, root8Node81Step1Chunk4_4_checked, root8Node81Step1Chunk4_5_checked, root8Node81Step1Chunk5_0_checked, root8Node81Step1Chunk5_1_checked, root8Node81Step1Chunk5_2_checked, root8Node81Step1Chunk5_3_checked, root8Node81Step1Chunk5_4_checked, root8Node81Step1Chunk5_5_checked, root8Node81Step1Chunk6_0_checked, root8Node81Step1Chunk6_1_checked, root8Node81Step1Chunk6_2_checked, root8Node81Step1Chunk6_3_checked, root8Node81Step1Chunk6_4_checked, root8Node81Step1Chunk6_5_checked, root8Node81Step1Chunk7_0_checked, root8Node81Step1Chunk7_1_checked, root8Node81Step1Chunk7_2_checked, root8Node81Step1Chunk7_3_checked, root8Node81Step1Chunk7_4_checked, root8Node81Step1Chunk7_5_checked, root8Node81Step1Chunk8_0_checked, root8Node81Step1Chunk8_1_checked, root8Node81Step1Chunk8_2_checked, root8Node81Step1Chunk8_3_checked, root8Node81Step1Chunk8_4_checked, root8Node81Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node81Step1_checked :
    checkReplacement table54 root8Node81Domains0 root8Node81Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node81Domains0 root8Node81Domains1
    root8Node81Domains0Fast root8Node81Domains1Fast
    root8Node81Domains0_fast_eq root8Node81Domains1_fast_eq
    root8Node81Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
