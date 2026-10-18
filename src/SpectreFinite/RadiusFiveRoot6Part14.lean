module

public import SpectreFinite.RadiusFiveRoot6Part13
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable52
public import SpectreFinite.RadiusFiveTable55
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node31Domains0 : Domains 91 State := restrict root6Node27Domains2 29 (3,5)
def root6Node31Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(8,4)]
  | 8 => some [(0,0)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(8,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(4,2)]
  | 22 => some [(5,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(3,5)]
  | 30 => some [(0,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,0),(2,4)]
  | 40 => some [(3,0)]
  | 41 => some [(2,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(3,1),(7,1)]
  | 50 => some [(0,1),(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(1,3),(6,3)]
  | 79 => some [(7,2),(8,2)]
  | 80 => some [(4,0),(8,0)]
  | 81 => some [(7,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(8,5)]
  | 85 => some [(0,4),(1,1)]
  | 86 => some [(5,1),(5,4)]
  | 87 => some [(0,1),(6,4)]
  | 88 => some [(1,2),(6,2)]
  | 89 => some [(7,4)]
  | _ => some [(6,3)]
theorem root6Node31Domains0_fast_eq : root6Node31Domains0 = expandDomains root6Node31Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node31Domains0 v = expandDomains root6Node31Domains0Fast v from by decide) v
def root6Node31Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0)]
  | 2 => [(4,5)]
  | 3 => [(7,0)]
  | 4 => [(4,3)]
  | 5 => [(7,5)]
  | 6 => [(1,2)]
  | 7 => [(8,4)]
  | 8 => [(0,0)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(1,3)]
  | 12 => [(8,2)]
  | 13 => [(0,3)]
  | 14 => [(8,1)]
  | 15 => [(1,5)]
  | 16 => [(6,1)]
  | 17 => [(8,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(5,4)]
  | 21 => [(4,2)]
  | 22 => [(5,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(4,3)]
  | 29 => [(3,5)]
  | 30 => [(0,4)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(2,4)]
  | 40 => [(3,0)]
  | 41 => [(2,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(7,1)]
  | 50 => [(6,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(8,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(6,1)]
  | 62 => [(5,1)]
  | 63 => [(0,1)]
  | 64 => [(6,2)]
  | 65 => [(8,4)]
  | 66 => [(6,4)]
  | 67 => [(1,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0)]
  | 70 => [(8,3)]
  | 71 => [(8,5)]
  | 72 => [(1,0)]
  | 73 => [(7,1)]
  | 74 => [(7,5)]
  | 75 => [(0,3)]
  | 76 => [(8,1)]
  | 77 => [(1,5)]
  | 78 => [(1,3),(6,3)]
  | 79 => [(7,2),(8,2)]
  | 80 => [(4,0)]
  | 81 => [(7,3)]
  | 82 => [(4,2)]
  | 83 => [(5,3)]
  | 84 => [(8,5)]
  | 85 => [(0,4),(1,1)]
  | 86 => [(5,1),(5,4)]
  | 87 => [(0,1)]
  | 88 => [(6,2)]
  | 89 => [(7,4)]
  | _ => [(6,3)]
def root6Node31Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(8,4)]
  | 8 => some [(0,0)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(8,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(4,2)]
  | 22 => some [(5,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(3,5)]
  | 30 => some [(0,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,4)]
  | 40 => some [(3,0)]
  | 41 => some [(2,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(1,3),(6,3)]
  | 79 => some [(7,2),(8,2)]
  | 80 => some [(4,0)]
  | 81 => some [(7,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(8,5)]
  | 85 => some [(0,4),(1,1)]
  | 86 => some [(5,1),(5,4)]
  | 87 => some [(0,1)]
  | 88 => some [(6,2)]
  | 89 => some [(7,4)]
  | _ => some [(6,3)]
theorem root6Node31Domains1_fast_eq : root6Node31Domains1 = expandDomains root6Node31Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node31Domains1 v = expandDomains root6Node31Domains1Fast v from by decide) v
theorem root6Node31Step1Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq (by decide)
theorem root6Node31Step1Narrowing_checked :
    checkNarrowing table57 root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root6Node31Domains0 root6Node31Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node31Step1Chunk0_0_checked, root6Node31Step1Chunk0_1_checked, root6Node31Step1Chunk0_2_checked, root6Node31Step1Chunk0_3_checked, root6Node31Step1Chunk0_4_checked, root6Node31Step1Chunk0_5_checked, root6Node31Step1Chunk1_0_checked, root6Node31Step1Chunk1_1_checked, root6Node31Step1Chunk1_2_checked, root6Node31Step1Chunk1_3_checked, root6Node31Step1Chunk1_4_checked, root6Node31Step1Chunk1_5_checked, root6Node31Step1Chunk2_0_checked, root6Node31Step1Chunk2_1_checked, root6Node31Step1Chunk2_2_checked, root6Node31Step1Chunk2_3_checked, root6Node31Step1Chunk2_4_checked, root6Node31Step1Chunk2_5_checked, root6Node31Step1Chunk3_0_checked, root6Node31Step1Chunk3_1_checked, root6Node31Step1Chunk3_2_checked, root6Node31Step1Chunk3_3_checked, root6Node31Step1Chunk3_4_checked, root6Node31Step1Chunk3_5_checked, root6Node31Step1Chunk4_0_checked, root6Node31Step1Chunk4_1_checked, root6Node31Step1Chunk4_2_checked, root6Node31Step1Chunk4_3_checked, root6Node31Step1Chunk4_4_checked, root6Node31Step1Chunk4_5_checked, root6Node31Step1Chunk5_0_checked, root6Node31Step1Chunk5_1_checked, root6Node31Step1Chunk5_2_checked, root6Node31Step1Chunk5_3_checked, root6Node31Step1Chunk5_4_checked, root6Node31Step1Chunk5_5_checked, root6Node31Step1Chunk6_0_checked, root6Node31Step1Chunk6_1_checked, root6Node31Step1Chunk6_2_checked, root6Node31Step1Chunk6_3_checked, root6Node31Step1Chunk6_4_checked, root6Node31Step1Chunk6_5_checked, root6Node31Step1Chunk7_0_checked, root6Node31Step1Chunk7_1_checked, root6Node31Step1Chunk7_2_checked, root6Node31Step1Chunk7_3_checked, root6Node31Step1Chunk7_4_checked, root6Node31Step1Chunk7_5_checked, root6Node31Step1Chunk8_0_checked, root6Node31Step1Chunk8_1_checked, root6Node31Step1Chunk8_2_checked, root6Node31Step1Chunk8_3_checked, root6Node31Step1Chunk8_4_checked, root6Node31Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node31Step1_checked :
    checkReplacement table57 root6Node31Domains0 root6Node31Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node31Domains0 root6Node31Domains1
    root6Node31Domains0Fast root6Node31Domains1Fast
    root6Node31Domains0_fast_eq root6Node31Domains1_fast_eq
    root6Node31Step1Narrowing_checked (by decide)
def root6Node31Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0)]
  | 2 => [(4,5)]
  | 3 => [(7,0)]
  | 4 => [(4,3)]
  | 5 => [(7,5)]
  | 6 => [(1,2)]
  | 7 => [(8,4)]
  | 8 => [(0,0)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(1,3)]
  | 12 => [(8,2)]
  | 13 => [(0,3)]
  | 14 => [(8,1)]
  | 15 => [(1,5)]
  | 16 => [(6,1)]
  | 17 => [(8,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(5,4)]
  | 21 => [(4,2)]
  | 22 => [(5,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(4,3)]
  | 29 => [(3,5)]
  | 30 => [(0,4)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(2,4)]
  | 40 => [(3,0)]
  | 41 => [(2,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(7,1)]
  | 50 => [(6,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(8,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(6,1)]
  | 62 => [(5,1)]
  | 63 => [(0,1)]
  | 64 => [(6,2)]
  | 65 => [(8,4)]
  | 66 => [(6,4)]
  | 67 => [(1,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0)]
  | 70 => [(8,3)]
  | 71 => [(8,5)]
  | 72 => [(1,0)]
  | 73 => [(7,1)]
  | 74 => [(7,5)]
  | 75 => [(0,3)]
  | 76 => [(8,1)]
  | 77 => [(1,5)]
  | 78 => [(6,3)]
  | 79 => [(7,2)]
  | 80 => [(4,0)]
  | 81 => [(7,3)]
  | 82 => [(4,2)]
  | 83 => [(5,3)]
  | 84 => [(8,5)]
  | 85 => [(1,1)]
  | 86 => [(5,1)]
  | 87 => [(0,1)]
  | 88 => [(6,2)]
  | 89 => [(7,4)]
  | _ => [(6,3)]
def root6Node31Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(1,2)]
  | 7 => some [(8,4)]
  | 8 => some [(0,0)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(8,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(4,2)]
  | 22 => some [(5,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(3,5)]
  | 30 => some [(0,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,4)]
  | 40 => some [(3,0)]
  | 41 => some [(2,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(4,0)]
  | 81 => some [(7,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(8,5)]
  | 85 => some [(1,1)]
  | 86 => some [(5,1)]
  | 87 => some [(0,1)]
  | 88 => some [(6,2)]
  | 89 => some [(7,4)]
  | _ => some [(6,3)]
theorem root6Node31Domains2_fast_eq : root6Node31Domains2 = expandDomains root6Node31Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node31Domains2 v = expandDomains root6Node31Domains2Fast v from by decide) v
theorem root6Node31Step2Chunk0_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_0⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk0_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_1⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk0_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_2⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk0_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_3⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk0_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_4⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk0_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_5⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk1_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_0⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk1_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_1⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk1_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_2⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk1_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_3⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk1_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_4⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk1_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_5⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk2_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_0⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk2_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_1⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk2_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_2⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk2_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_3⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk2_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_4⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk2_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_5⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk3_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_0⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk3_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_1⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk3_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_2⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk3_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_3⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk3_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_4⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk3_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_5⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk4_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_0⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk4_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_1⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk4_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_2⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk4_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_3⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk4_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_4⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk4_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_5⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk5_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_0⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk5_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_1⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk5_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_2⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk5_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_3⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk5_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_4⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk5_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_5⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk6_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_0⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk6_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_1⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk6_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_2⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk6_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_3⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk6_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_4⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk6_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_5⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk7_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_0⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk7_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_1⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk7_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_2⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk7_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_3⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk7_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_4⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk7_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_5⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk8_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_0⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk8_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_1⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk8_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_2⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk8_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_3⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk8_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_4⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Chunk8_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_5⟩
      root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq (by decide)
theorem root6Node31Step2Narrowing_checked :
    checkNarrowing table52 root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkNarrowing_flatten table52Scope [table52Rows0_0,table52Rows0_1,table52Rows0_2,table52Rows0_3,table52Rows0_4,table52Rows0_5,table52Rows1_0,table52Rows1_1,table52Rows1_2,table52Rows1_3,table52Rows1_4,table52Rows1_5,table52Rows2_0,table52Rows2_1,table52Rows2_2,table52Rows2_3,table52Rows2_4,table52Rows2_5,table52Rows3_0,table52Rows3_1,table52Rows3_2,table52Rows3_3,table52Rows3_4,table52Rows3_5,table52Rows4_0,table52Rows4_1,table52Rows4_2,table52Rows4_3,table52Rows4_4,table52Rows4_5,table52Rows5_0,table52Rows5_1,table52Rows5_2,table52Rows5_3,table52Rows5_4,table52Rows5_5,table52Rows6_0,table52Rows6_1,table52Rows6_2,table52Rows6_3,table52Rows6_4,table52Rows6_5,table52Rows7_0,table52Rows7_1,table52Rows7_2,table52Rows7_3,table52Rows7_4,table52Rows7_5,table52Rows8_0,table52Rows8_1,table52Rows8_2,table52Rows8_3,table52Rows8_4,table52Rows8_5]
    root6Node31Domains1 root6Node31Domains2 (by
      simp only [List.all_cons, List.all_nil, root6Node31Step2Chunk0_0_checked, root6Node31Step2Chunk0_1_checked, root6Node31Step2Chunk0_2_checked, root6Node31Step2Chunk0_3_checked, root6Node31Step2Chunk0_4_checked, root6Node31Step2Chunk0_5_checked, root6Node31Step2Chunk1_0_checked, root6Node31Step2Chunk1_1_checked, root6Node31Step2Chunk1_2_checked, root6Node31Step2Chunk1_3_checked, root6Node31Step2Chunk1_4_checked, root6Node31Step2Chunk1_5_checked, root6Node31Step2Chunk2_0_checked, root6Node31Step2Chunk2_1_checked, root6Node31Step2Chunk2_2_checked, root6Node31Step2Chunk2_3_checked, root6Node31Step2Chunk2_4_checked, root6Node31Step2Chunk2_5_checked, root6Node31Step2Chunk3_0_checked, root6Node31Step2Chunk3_1_checked, root6Node31Step2Chunk3_2_checked, root6Node31Step2Chunk3_3_checked, root6Node31Step2Chunk3_4_checked, root6Node31Step2Chunk3_5_checked, root6Node31Step2Chunk4_0_checked, root6Node31Step2Chunk4_1_checked, root6Node31Step2Chunk4_2_checked, root6Node31Step2Chunk4_3_checked, root6Node31Step2Chunk4_4_checked, root6Node31Step2Chunk4_5_checked, root6Node31Step2Chunk5_0_checked, root6Node31Step2Chunk5_1_checked, root6Node31Step2Chunk5_2_checked, root6Node31Step2Chunk5_3_checked, root6Node31Step2Chunk5_4_checked, root6Node31Step2Chunk5_5_checked, root6Node31Step2Chunk6_0_checked, root6Node31Step2Chunk6_1_checked, root6Node31Step2Chunk6_2_checked, root6Node31Step2Chunk6_3_checked, root6Node31Step2Chunk6_4_checked, root6Node31Step2Chunk6_5_checked, root6Node31Step2Chunk7_0_checked, root6Node31Step2Chunk7_1_checked, root6Node31Step2Chunk7_2_checked, root6Node31Step2Chunk7_3_checked, root6Node31Step2Chunk7_4_checked, root6Node31Step2Chunk7_5_checked, root6Node31Step2Chunk8_0_checked, root6Node31Step2Chunk8_1_checked, root6Node31Step2Chunk8_2_checked, root6Node31Step2Chunk8_3_checked, root6Node31Step2Chunk8_4_checked, root6Node31Step2Chunk8_5_checked, Bool.true_and])
theorem root6Node31Step2_checked :
    checkReplacement table52 root6Node31Domains1 root6Node31Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root6Node31Domains1 root6Node31Domains2
    root6Node31Domains1Fast root6Node31Domains2Fast
    root6Node31Domains1_fast_eq root6Node31Domains2_fast_eq
    root6Node31Step2Narrowing_checked (by decide)
theorem root6Node31Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node31Domains2 (.output 14) = true := by decide
def root6Node32Domains0 : Domains 91 State := restrict root6Node20Domains1 4 (8,3)
def root6Node32Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(7,5),(8,5)]
  | 6 => some [(1,2)]
  | 7 => some [(8,4)]
  | 8 => some [(0,0)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(4,2),(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(8,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(1,4),(3,4),(5,4)]
  | 21 => some [(4,2)]
  | 22 => some [(5,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(3,0),(7,0)]
  | 28 => some [(2,3),(2,5),(4,3)]
  | 29 => some [(0,2),(1,5),(3,5),(6,0)]
  | 30 => some [(0,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0),(1,4),(6,4)]
  | 38 => some [(0,5),(1,2),(7,2)]
  | 39 => some [(2,0),(2,4),(4,0)]
  | 40 => some [(3,0)]
  | 41 => some [(2,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5),(7,5)]
  | 48 => some [(0,3),(6,0),(6,1)]
  | 49 => some [(3,1),(5,1),(7,1)]
  | 50 => some [(0,1),(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(4,2),(7,0),(8,2)]
  | 59 => some [(5,0),(5,3),(8,3)]
  | 60 => some [(4,5),(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0),(6,4)]
  | 67 => some [(1,2),(7,2)]
  | 68 => some [(7,4),(8,4)]
  | 69 => some [(0,0),(1,3)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(1,5),(7,5)]
  | 75 => some [(0,3),(6,1)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5),(6,5)]
  | 78 => some [(1,3),(6,3)]
  | 79 => some [(7,2),(8,2)]
  | 80 => some [(4,0),(5,0),(8,0)]
  | 81 => some [(4,5),(7,3)]
  | 82 => some [(4,2),(7,0)]
  | 83 => some [(5,3),(8,3)]
  | 84 => some [(8,5)]
  | 85 => some [(0,4),(1,1)]
  | 86 => some [(5,1),(5,4)]
  | 87 => some [(0,0),(0,1),(6,4)]
  | 88 => some [(1,2),(6,2),(7,2)]
  | 89 => some [(7,4)]
  | _ => some [(6,3)]
theorem root6Node32Domains0_fast_eq : root6Node32Domains0 = expandDomains root6Node32Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node32Domains0 v = expandDomains root6Node32Domains0Fast v from by decide) v
def root6Node32Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0)]
  | 2 => [(4,5)]
  | 3 => [(7,0)]
  | 4 => [(8,3)]
  | 5 => [(8,5)]
  | 6 => [(1,2)]
  | 7 => [(8,4)]
  | 8 => [(0,0)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(1,3)]
  | 12 => [(8,2)]
  | 13 => [(0,3)]
  | 14 => [(8,1)]
  | 15 => [(1,5)]
  | 16 => [(6,1)]
  | 17 => [(8,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(5,4)]
  | 21 => [(4,2)]
  | 22 => [(5,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(4,3)]
  | 29 => [(1,5),(3,5)]
  | 30 => [(0,4)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(2,0),(2,4)]
  | 40 => [(3,0)]
  | 41 => [(2,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(3,1),(7,1)]
  | 50 => [(0,1),(6,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(8,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(6,1)]
  | 62 => [(5,1)]
  | 63 => [(0,1)]
  | 64 => [(6,2)]
  | 65 => [(8,4)]
  | 66 => [(6,4)]
  | 67 => [(1,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0)]
  | 70 => [(8,3)]
  | 71 => [(8,5)]
  | 72 => [(1,0)]
  | 73 => [(7,1)]
  | 74 => [(7,5)]
  | 75 => [(0,3)]
  | 76 => [(8,1)]
  | 77 => [(1,5)]
  | 78 => [(1,3),(6,3)]
  | 79 => [(7,2),(8,2)]
  | 80 => [(4,0),(5,0),(8,0)]
  | 81 => [(4,5),(7,3)]
  | 82 => [(4,2),(7,0)]
  | 83 => [(5,3),(8,3)]
  | 84 => [(8,5)]
  | 85 => [(0,4),(1,1)]
  | 86 => [(5,1),(5,4)]
  | 87 => [(0,0),(0,1),(6,4)]
  | 88 => [(1,2),(6,2),(7,2)]
  | 89 => [(7,4)]
  | _ => [(6,3)]
def root6Node32Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(8,5)]
  | 6 => some [(1,2)]
  | 7 => some [(8,4)]
  | 8 => some [(0,0)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(8,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(4,2)]
  | 22 => some [(5,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(1,5),(3,5)]
  | 30 => some [(0,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,0),(2,4)]
  | 40 => some [(3,0)]
  | 41 => some [(2,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(3,1),(7,1)]
  | 50 => some [(0,1),(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(1,3),(6,3)]
  | 79 => some [(7,2),(8,2)]
  | 80 => some [(4,0),(5,0),(8,0)]
  | 81 => some [(4,5),(7,3)]
  | 82 => some [(4,2),(7,0)]
  | 83 => some [(5,3),(8,3)]
  | 84 => some [(8,5)]
  | 85 => some [(0,4),(1,1)]
  | 86 => some [(5,1),(5,4)]
  | 87 => some [(0,0),(0,1),(6,4)]
  | 88 => some [(1,2),(6,2),(7,2)]
  | 89 => some [(7,4)]
  | _ => some [(6,3)]
theorem root6Node32Domains1_fast_eq : root6Node32Domains1 = expandDomains root6Node32Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node32Domains1 v = expandDomains root6Node32Domains1Fast v from by decide) v
theorem root6Node32Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq (by decide)
theorem root6Node32Step1Narrowing_checked :
    checkNarrowing table36 root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root6Node32Domains0 root6Node32Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node32Step1Chunk0_0_checked, root6Node32Step1Chunk0_1_checked, root6Node32Step1Chunk0_2_checked, root6Node32Step1Chunk0_3_checked, root6Node32Step1Chunk0_4_checked, root6Node32Step1Chunk0_5_checked, root6Node32Step1Chunk1_0_checked, root6Node32Step1Chunk1_1_checked, root6Node32Step1Chunk1_2_checked, root6Node32Step1Chunk1_3_checked, root6Node32Step1Chunk1_4_checked, root6Node32Step1Chunk1_5_checked, root6Node32Step1Chunk2_0_checked, root6Node32Step1Chunk2_1_checked, root6Node32Step1Chunk2_2_checked, root6Node32Step1Chunk2_3_checked, root6Node32Step1Chunk2_4_checked, root6Node32Step1Chunk2_5_checked, root6Node32Step1Chunk3_0_checked, root6Node32Step1Chunk3_1_checked, root6Node32Step1Chunk3_2_checked, root6Node32Step1Chunk3_3_checked, root6Node32Step1Chunk3_4_checked, root6Node32Step1Chunk3_5_checked, root6Node32Step1Chunk4_0_checked, root6Node32Step1Chunk4_1_checked, root6Node32Step1Chunk4_2_checked, root6Node32Step1Chunk4_3_checked, root6Node32Step1Chunk4_4_checked, root6Node32Step1Chunk4_5_checked, root6Node32Step1Chunk5_0_checked, root6Node32Step1Chunk5_1_checked, root6Node32Step1Chunk5_2_checked, root6Node32Step1Chunk5_3_checked, root6Node32Step1Chunk5_4_checked, root6Node32Step1Chunk5_5_checked, root6Node32Step1Chunk6_0_checked, root6Node32Step1Chunk6_1_checked, root6Node32Step1Chunk6_2_checked, root6Node32Step1Chunk6_3_checked, root6Node32Step1Chunk6_4_checked, root6Node32Step1Chunk6_5_checked, root6Node32Step1Chunk7_0_checked, root6Node32Step1Chunk7_1_checked, root6Node32Step1Chunk7_2_checked, root6Node32Step1Chunk7_3_checked, root6Node32Step1Chunk7_4_checked, root6Node32Step1Chunk7_5_checked, root6Node32Step1Chunk8_0_checked, root6Node32Step1Chunk8_1_checked, root6Node32Step1Chunk8_2_checked, root6Node32Step1Chunk8_3_checked, root6Node32Step1Chunk8_4_checked, root6Node32Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node32Step1_checked :
    checkReplacement table36 root6Node32Domains0 root6Node32Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node32Domains0 root6Node32Domains1
    root6Node32Domains0Fast root6Node32Domains1Fast
    root6Node32Domains0_fast_eq root6Node32Domains1_fast_eq
    root6Node32Step1Narrowing_checked (by decide)
def root6Node32Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0)]
  | 2 => [(4,5)]
  | 3 => [(7,0)]
  | 4 => [(8,3)]
  | 5 => [(8,5)]
  | 6 => [(1,2)]
  | 7 => [(8,4)]
  | 8 => [(0,0)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(1,3)]
  | 12 => [(8,2)]
  | 13 => [(0,3)]
  | 14 => [(8,1)]
  | 15 => [(1,5)]
  | 16 => [(6,1)]
  | 17 => [(8,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(5,4)]
  | 21 => [(4,2)]
  | 22 => [(5,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(4,3)]
  | 29 => [(1,5),(3,5)]
  | 30 => [(0,4)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(2,0),(2,4)]
  | 40 => [(3,0)]
  | 41 => [(2,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(3,1),(7,1)]
  | 50 => [(0,1),(6,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(4,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(8,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(6,1)]
  | 62 => [(5,1)]
  | 63 => [(0,1)]
  | 64 => [(6,2)]
  | 65 => [(8,4)]
  | 66 => [(6,4)]
  | 67 => [(1,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0)]
  | 70 => [(8,3)]
  | 71 => [(8,5)]
  | 72 => [(1,0)]
  | 73 => [(7,1)]
  | 74 => [(7,5)]
  | 75 => [(0,3)]
  | 76 => [(8,1)]
  | 77 => [(1,5)]
  | 78 => [(1,3),(6,3)]
  | 79 => [(7,2),(8,2)]
  | 80 => [(4,0),(8,0)]
  | 81 => [(7,3)]
  | 82 => [(4,2)]
  | 83 => [(5,3)]
  | 84 => [(8,5)]
  | 85 => [(0,4),(1,1)]
  | 86 => [(5,1),(5,4)]
  | 87 => [(0,1),(6,4)]
  | 88 => [(1,2),(6,2)]
  | 89 => [(7,4)]
  | _ => [(6,3)]
def root6Node32Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(8,5)]
  | 6 => some [(1,2)]
  | 7 => some [(8,4)]
  | 8 => some [(0,0)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(8,2)]
  | 13 => some [(0,3)]
  | 14 => some [(8,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(5,4)]
  | 21 => some [(4,2)]
  | 22 => some [(5,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3)]
  | 29 => some [(1,5),(3,5)]
  | 30 => some [(0,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,0),(2,4)]
  | 40 => some [(3,0)]
  | 41 => some [(2,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(3,1),(7,1)]
  | 50 => some [(0,1),(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(4,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(6,1)]
  | 62 => some [(5,1)]
  | 63 => some [(0,1)]
  | 64 => some [(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(8,3)]
  | 71 => some [(8,5)]
  | 72 => some [(1,0)]
  | 73 => some [(7,1)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(1,3),(6,3)]
  | 79 => some [(7,2),(8,2)]
  | 80 => some [(4,0),(8,0)]
  | 81 => some [(7,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(8,5)]
  | 85 => some [(0,4),(1,1)]
  | 86 => some [(5,1),(5,4)]
  | 87 => some [(0,1),(6,4)]
  | 88 => some [(1,2),(6,2)]
  | 89 => some [(7,4)]
  | _ => some [(6,3)]
theorem root6Node32Domains2_fast_eq : root6Node32Domains2 = expandDomains root6Node32Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node32Domains2 v = expandDomains root6Node32Domains2Fast v from by decide) v
theorem root6Node32Step2Chunk0_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_0⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk0_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_1⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk0_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_2⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk0_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_3⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk0_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_4⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk0_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_5⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk1_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_0⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk1_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_1⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk1_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_2⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk1_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_3⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk1_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_4⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk1_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_5⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk2_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_0⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk2_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_1⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk2_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_2⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk2_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_3⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk2_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_4⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk2_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_5⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk3_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_0⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk3_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_1⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk3_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_2⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk3_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_3⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk3_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_4⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk3_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_5⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk4_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_0⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk4_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_1⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk4_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_2⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk4_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_3⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk4_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_4⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk4_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_5⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk5_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_0⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk5_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_1⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk5_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_2⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk5_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_3⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk5_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_4⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk5_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_5⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk6_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_0⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk6_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_1⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk6_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_2⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk6_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_3⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk6_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_4⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk6_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_5⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk7_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_0⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk7_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_1⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk7_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_2⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk7_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_3⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk7_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_4⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk7_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_5⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk8_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_0⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk8_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_1⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk8_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_2⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk8_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_3⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk8_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_4⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Chunk8_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_5⟩
      root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq (by decide)
theorem root6Node32Step2Narrowing_checked :
    checkNarrowing table55 root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkNarrowing_flatten table55Scope [table55Rows0_0,table55Rows0_1,table55Rows0_2,table55Rows0_3,table55Rows0_4,table55Rows0_5,table55Rows1_0,table55Rows1_1,table55Rows1_2,table55Rows1_3,table55Rows1_4,table55Rows1_5,table55Rows2_0,table55Rows2_1,table55Rows2_2,table55Rows2_3,table55Rows2_4,table55Rows2_5,table55Rows3_0,table55Rows3_1,table55Rows3_2,table55Rows3_3,table55Rows3_4,table55Rows3_5,table55Rows4_0,table55Rows4_1,table55Rows4_2,table55Rows4_3,table55Rows4_4,table55Rows4_5,table55Rows5_0,table55Rows5_1,table55Rows5_2,table55Rows5_3,table55Rows5_4,table55Rows5_5,table55Rows6_0,table55Rows6_1,table55Rows6_2,table55Rows6_3,table55Rows6_4,table55Rows6_5,table55Rows7_0,table55Rows7_1,table55Rows7_2,table55Rows7_3,table55Rows7_4,table55Rows7_5,table55Rows8_0,table55Rows8_1,table55Rows8_2,table55Rows8_3,table55Rows8_4,table55Rows8_5]
    root6Node32Domains1 root6Node32Domains2 (by
      simp only [List.all_cons, List.all_nil, root6Node32Step2Chunk0_0_checked, root6Node32Step2Chunk0_1_checked, root6Node32Step2Chunk0_2_checked, root6Node32Step2Chunk0_3_checked, root6Node32Step2Chunk0_4_checked, root6Node32Step2Chunk0_5_checked, root6Node32Step2Chunk1_0_checked, root6Node32Step2Chunk1_1_checked, root6Node32Step2Chunk1_2_checked, root6Node32Step2Chunk1_3_checked, root6Node32Step2Chunk1_4_checked, root6Node32Step2Chunk1_5_checked, root6Node32Step2Chunk2_0_checked, root6Node32Step2Chunk2_1_checked, root6Node32Step2Chunk2_2_checked, root6Node32Step2Chunk2_3_checked, root6Node32Step2Chunk2_4_checked, root6Node32Step2Chunk2_5_checked, root6Node32Step2Chunk3_0_checked, root6Node32Step2Chunk3_1_checked, root6Node32Step2Chunk3_2_checked, root6Node32Step2Chunk3_3_checked, root6Node32Step2Chunk3_4_checked, root6Node32Step2Chunk3_5_checked, root6Node32Step2Chunk4_0_checked, root6Node32Step2Chunk4_1_checked, root6Node32Step2Chunk4_2_checked, root6Node32Step2Chunk4_3_checked, root6Node32Step2Chunk4_4_checked, root6Node32Step2Chunk4_5_checked, root6Node32Step2Chunk5_0_checked, root6Node32Step2Chunk5_1_checked, root6Node32Step2Chunk5_2_checked, root6Node32Step2Chunk5_3_checked, root6Node32Step2Chunk5_4_checked, root6Node32Step2Chunk5_5_checked, root6Node32Step2Chunk6_0_checked, root6Node32Step2Chunk6_1_checked, root6Node32Step2Chunk6_2_checked, root6Node32Step2Chunk6_3_checked, root6Node32Step2Chunk6_4_checked, root6Node32Step2Chunk6_5_checked, root6Node32Step2Chunk7_0_checked, root6Node32Step2Chunk7_1_checked, root6Node32Step2Chunk7_2_checked, root6Node32Step2Chunk7_3_checked, root6Node32Step2Chunk7_4_checked, root6Node32Step2Chunk7_5_checked, root6Node32Step2Chunk8_0_checked, root6Node32Step2Chunk8_1_checked, root6Node32Step2Chunk8_2_checked, root6Node32Step2Chunk8_3_checked, root6Node32Step2Chunk8_4_checked, root6Node32Step2Chunk8_5_checked, Bool.true_and])
theorem root6Node32Step2_checked :
    checkReplacement table55 root6Node32Domains1 root6Node32Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root6Node32Domains1 root6Node32Domains2
    root6Node32Domains1Fast root6Node32Domains2Fast
    root6Node32Domains1_fast_eq root6Node32Domains2_fast_eq
    root6Node32Step2Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
