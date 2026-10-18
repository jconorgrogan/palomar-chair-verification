module

public import SpectreFinite.RadiusFiveRoot7Part40
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable51
public import SpectreFinite.RadiusFiveTable52
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node104Domains0 : Domains 91 State := restrict root7Node102Domains2 40 (8,0)
def root7Node104Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,2)]
  | 1 => some [(7,4)]
  | 2 => some [(1,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(5,5)]
  | 6 => some [(1,1)]
  | 7 => some [(8,1)]
  | 8 => some [(6,5)]
  | 9 => some [(0,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(8,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(1,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5),(7,5)]
  | 51 => some [(0,1),(6,4)]
  | 52 => some [(1,2),(6,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0),(8,0)]
  | 60 => some [(4,5),(7,3)]
  | 61 => some [(0,3),(1,0)]
  | 62 => some [(7,1),(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(5,4)]
  | 69 => some [(0,0),(6,4)]
  | 70 => some [(5,0),(5,3)]
  | 71 => some [(4,5),(5,5),(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5),(8,5)]
  | 75 => some [(7,0)]
  | 76 => some [(4,3)]
  | 77 => some [(1,5),(3,5),(7,5)]
  | 78 => some [(0,0),(0,5),(6,3)]
  | 79 => some [(4,4),(7,2)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(6,3)]
  | 82 => some [(4,4),(7,2)]
  | 83 => some [(1,4),(7,4)]
  | 84 => some [(0,5),(6,3)]
  | 85 => some [(1,1),(6,1),(7,1)]
  | 86 => some [(4,1),(7,5)]
  | 87 => some [(0,2),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(4,1),(7,5)]
  | _ => some [(0,2),(6,0)]
theorem root7Node104Domains0_fast_eq : root7Node104Domains0 = expandDomains root7Node104Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node104Domains0 v = expandDomains root7Node104Domains0Fast v from by decide) v
def root7Node104Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,2)]
  | 1 => [(7,4)]
  | 2 => [(1,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(5,5)]
  | 6 => [(1,1)]
  | 7 => [(8,1)]
  | 8 => [(6,5)]
  | 9 => [(0,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(3,0)]
  | 17 => [(2,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(4,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(5,1)]
  | 37 => [(0,1)]
  | 38 => [(6,2)]
  | 39 => [(8,4)]
  | 40 => [(8,0)]
  | 41 => [(7,3)]
  | 42 => [(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(8,5)]
  | 48 => [(1,0)]
  | 49 => [(7,1)]
  | 50 => [(1,5),(7,5)]
  | 51 => [(6,4)]
  | 52 => [(1,2)]
  | 53 => [(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0),(8,0)]
  | 60 => [(4,5),(7,3)]
  | 61 => [(0,3)]
  | 62 => [(8,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(8,1)]
  | 66 => [(6,5)]
  | 67 => [(0,4)]
  | 68 => [(5,4)]
  | 69 => [(0,0),(6,4)]
  | 70 => [(5,3)]
  | 71 => [(5,5),(8,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5),(8,5)]
  | 75 => [(7,0)]
  | 76 => [(4,3)]
  | 77 => [(1,5),(3,5),(7,5)]
  | 78 => [(0,5),(6,3)]
  | 79 => [(4,4),(7,2)]
  | 80 => [(1,4),(7,4)]
  | 81 => [(0,5),(6,3)]
  | 82 => [(4,4),(7,2)]
  | 83 => [(1,4),(7,4)]
  | 84 => [(0,5),(6,3)]
  | 85 => [(1,1),(7,1)]
  | 86 => [(4,1),(7,5)]
  | 87 => [(0,2),(6,0)]
  | 88 => [(1,1),(7,1)]
  | 89 => [(4,1),(7,5)]
  | _ => [(0,2),(6,0)]
def root7Node104Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,2)]
  | 1 => some [(7,4)]
  | 2 => some [(1,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(5,5)]
  | 6 => some [(1,1)]
  | 7 => some [(8,1)]
  | 8 => some [(6,5)]
  | 9 => some [(0,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(8,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(1,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5),(7,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0),(8,0)]
  | 60 => some [(4,5),(7,3)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(5,4)]
  | 69 => some [(0,0),(6,4)]
  | 70 => some [(5,3)]
  | 71 => some [(5,5),(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5),(8,5)]
  | 75 => some [(7,0)]
  | 76 => some [(4,3)]
  | 77 => some [(1,5),(3,5),(7,5)]
  | 78 => some [(0,5),(6,3)]
  | 79 => some [(4,4),(7,2)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(6,3)]
  | 82 => some [(4,4),(7,2)]
  | 83 => some [(1,4),(7,4)]
  | 84 => some [(0,5),(6,3)]
  | 85 => some [(1,1),(7,1)]
  | 86 => some [(4,1),(7,5)]
  | 87 => some [(0,2),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(4,1),(7,5)]
  | _ => some [(0,2),(6,0)]
theorem root7Node104Domains1_fast_eq : root7Node104Domains1 = expandDomains root7Node104Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node104Domains1 v = expandDomains root7Node104Domains1Fast v from by decide) v
theorem root7Node104Step1Chunk0_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_0⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk0_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_1⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk0_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_2⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk0_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_3⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk0_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_4⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk0_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_5⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk1_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_0⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk1_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_1⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk1_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_2⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk1_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_3⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk1_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_4⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk1_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_5⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk2_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_0⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk2_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_1⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk2_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_2⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk2_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_3⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk2_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_4⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk2_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_5⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk3_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_0⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk3_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_1⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk3_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_2⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk3_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_3⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk3_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_4⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk3_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_5⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk4_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_0⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk4_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_1⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk4_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_2⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk4_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_3⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk4_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_4⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk4_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_5⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk5_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_0⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk5_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_1⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk5_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_2⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk5_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_3⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk5_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_4⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk5_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_5⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk6_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_0⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk6_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_1⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk6_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_2⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk6_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_3⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk6_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_4⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk6_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_5⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk7_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_0⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk7_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_1⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk7_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_2⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk7_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_3⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk7_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_4⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk7_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_5⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk8_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_0⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk8_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_1⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk8_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_2⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk8_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_3⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk8_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_4⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Chunk8_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_5⟩
      root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq (by decide)
theorem root7Node104Step1Narrowing_checked :
    checkNarrowing table51 root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkNarrowing_flatten table51Scope [table51Rows0_0,table51Rows0_1,table51Rows0_2,table51Rows0_3,table51Rows0_4,table51Rows0_5,table51Rows1_0,table51Rows1_1,table51Rows1_2,table51Rows1_3,table51Rows1_4,table51Rows1_5,table51Rows2_0,table51Rows2_1,table51Rows2_2,table51Rows2_3,table51Rows2_4,table51Rows2_5,table51Rows3_0,table51Rows3_1,table51Rows3_2,table51Rows3_3,table51Rows3_4,table51Rows3_5,table51Rows4_0,table51Rows4_1,table51Rows4_2,table51Rows4_3,table51Rows4_4,table51Rows4_5,table51Rows5_0,table51Rows5_1,table51Rows5_2,table51Rows5_3,table51Rows5_4,table51Rows5_5,table51Rows6_0,table51Rows6_1,table51Rows6_2,table51Rows6_3,table51Rows6_4,table51Rows6_5,table51Rows7_0,table51Rows7_1,table51Rows7_2,table51Rows7_3,table51Rows7_4,table51Rows7_5,table51Rows8_0,table51Rows8_1,table51Rows8_2,table51Rows8_3,table51Rows8_4,table51Rows8_5]
    root7Node104Domains0 root7Node104Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node104Step1Chunk0_0_checked, root7Node104Step1Chunk0_1_checked, root7Node104Step1Chunk0_2_checked, root7Node104Step1Chunk0_3_checked, root7Node104Step1Chunk0_4_checked, root7Node104Step1Chunk0_5_checked, root7Node104Step1Chunk1_0_checked, root7Node104Step1Chunk1_1_checked, root7Node104Step1Chunk1_2_checked, root7Node104Step1Chunk1_3_checked, root7Node104Step1Chunk1_4_checked, root7Node104Step1Chunk1_5_checked, root7Node104Step1Chunk2_0_checked, root7Node104Step1Chunk2_1_checked, root7Node104Step1Chunk2_2_checked, root7Node104Step1Chunk2_3_checked, root7Node104Step1Chunk2_4_checked, root7Node104Step1Chunk2_5_checked, root7Node104Step1Chunk3_0_checked, root7Node104Step1Chunk3_1_checked, root7Node104Step1Chunk3_2_checked, root7Node104Step1Chunk3_3_checked, root7Node104Step1Chunk3_4_checked, root7Node104Step1Chunk3_5_checked, root7Node104Step1Chunk4_0_checked, root7Node104Step1Chunk4_1_checked, root7Node104Step1Chunk4_2_checked, root7Node104Step1Chunk4_3_checked, root7Node104Step1Chunk4_4_checked, root7Node104Step1Chunk4_5_checked, root7Node104Step1Chunk5_0_checked, root7Node104Step1Chunk5_1_checked, root7Node104Step1Chunk5_2_checked, root7Node104Step1Chunk5_3_checked, root7Node104Step1Chunk5_4_checked, root7Node104Step1Chunk5_5_checked, root7Node104Step1Chunk6_0_checked, root7Node104Step1Chunk6_1_checked, root7Node104Step1Chunk6_2_checked, root7Node104Step1Chunk6_3_checked, root7Node104Step1Chunk6_4_checked, root7Node104Step1Chunk6_5_checked, root7Node104Step1Chunk7_0_checked, root7Node104Step1Chunk7_1_checked, root7Node104Step1Chunk7_2_checked, root7Node104Step1Chunk7_3_checked, root7Node104Step1Chunk7_4_checked, root7Node104Step1Chunk7_5_checked, root7Node104Step1Chunk8_0_checked, root7Node104Step1Chunk8_1_checked, root7Node104Step1Chunk8_2_checked, root7Node104Step1Chunk8_3_checked, root7Node104Step1Chunk8_4_checked, root7Node104Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node104Step1_checked :
    checkReplacement table51 root7Node104Domains0 root7Node104Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node104Domains0 root7Node104Domains1
    root7Node104Domains0Fast root7Node104Domains1Fast
    root7Node104Domains0_fast_eq root7Node104Domains1_fast_eq
    root7Node104Step1Narrowing_checked (by decide)
def root7Node105Domains0 : Domains 91 State := restrict root7Node104Domains1 50 (1,5)
def root7Node105Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,2)]
  | 1 => some [(7,4)]
  | 2 => some [(1,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(5,5)]
  | 6 => some [(1,1)]
  | 7 => some [(8,1)]
  | 8 => some [(6,5)]
  | 9 => some [(0,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(8,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(1,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0),(8,0)]
  | 60 => some [(4,5),(7,3)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(5,4)]
  | 69 => some [(0,0),(6,4)]
  | 70 => some [(5,3)]
  | 71 => some [(5,5),(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5),(8,5)]
  | 75 => some [(7,0)]
  | 76 => some [(4,3)]
  | 77 => some [(1,5),(3,5),(7,5)]
  | 78 => some [(0,5),(6,3)]
  | 79 => some [(4,4),(7,2)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(6,3)]
  | 82 => some [(4,4),(7,2)]
  | 83 => some [(1,4),(7,4)]
  | 84 => some [(0,5),(6,3)]
  | 85 => some [(1,1),(7,1)]
  | 86 => some [(4,1),(7,5)]
  | 87 => some [(0,2),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(4,1),(7,5)]
  | _ => some [(0,2),(6,0)]
theorem root7Node105Domains0_fast_eq : root7Node105Domains0 = expandDomains root7Node105Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node105Domains0 v = expandDomains root7Node105Domains0Fast v from by decide) v
def root7Node105Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,2)]
  | 1 => [(7,4)]
  | 2 => [(1,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(5,5)]
  | 6 => [(1,1)]
  | 7 => [(8,1)]
  | 8 => [(6,5)]
  | 9 => [(0,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(3,0)]
  | 17 => [(2,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(4,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(5,1)]
  | 37 => [(0,1)]
  | 38 => [(6,2)]
  | 39 => [(8,4)]
  | 40 => [(8,0)]
  | 41 => [(7,3)]
  | 42 => [(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(8,5)]
  | 48 => [(1,0)]
  | 49 => [(7,1)]
  | 50 => [(1,5)]
  | 51 => [(6,4)]
  | 52 => [(1,2)]
  | 53 => [(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(0,3)]
  | 62 => [(8,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(8,1)]
  | 66 => [(6,5)]
  | 67 => [(0,4)]
  | 68 => [(5,4)]
  | 69 => [(0,0)]
  | 70 => [(5,3)]
  | 71 => [(5,5),(8,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5)]
  | 75 => [(7,0)]
  | 76 => [(4,3)]
  | 77 => [(1,5)]
  | 78 => [(0,5),(6,3)]
  | 79 => [(4,4),(7,2)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(4,4)]
  | 83 => [(1,4)]
  | 84 => [(0,5)]
  | 85 => [(1,1),(7,1)]
  | 86 => [(4,1),(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(7,5)]
  | _ => [(6,0)]
def root7Node105Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,2)]
  | 1 => some [(7,4)]
  | 2 => some [(1,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(5,5)]
  | 6 => some [(1,1)]
  | 7 => some [(8,1)]
  | 8 => some [(6,5)]
  | 9 => some [(0,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(8,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(1,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(5,4)]
  | 69 => some [(0,0)]
  | 70 => some [(5,3)]
  | 71 => some [(5,5),(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(7,0)]
  | 76 => some [(4,3)]
  | 77 => some [(1,5)]
  | 78 => some [(0,5),(6,3)]
  | 79 => some [(4,4),(7,2)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(1,4)]
  | 84 => some [(0,5)]
  | 85 => some [(1,1),(7,1)]
  | 86 => some [(4,1),(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(6,0)]
theorem root7Node105Domains1_fast_eq : root7Node105Domains1 = expandDomains root7Node105Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node105Domains1 v = expandDomains root7Node105Domains1Fast v from by decide) v
theorem root7Node105Step1Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq (by decide)
theorem root7Node105Step1Narrowing_checked :
    checkNarrowing table57 root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root7Node105Domains0 root7Node105Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node105Step1Chunk0_0_checked, root7Node105Step1Chunk0_1_checked, root7Node105Step1Chunk0_2_checked, root7Node105Step1Chunk0_3_checked, root7Node105Step1Chunk0_4_checked, root7Node105Step1Chunk0_5_checked, root7Node105Step1Chunk1_0_checked, root7Node105Step1Chunk1_1_checked, root7Node105Step1Chunk1_2_checked, root7Node105Step1Chunk1_3_checked, root7Node105Step1Chunk1_4_checked, root7Node105Step1Chunk1_5_checked, root7Node105Step1Chunk2_0_checked, root7Node105Step1Chunk2_1_checked, root7Node105Step1Chunk2_2_checked, root7Node105Step1Chunk2_3_checked, root7Node105Step1Chunk2_4_checked, root7Node105Step1Chunk2_5_checked, root7Node105Step1Chunk3_0_checked, root7Node105Step1Chunk3_1_checked, root7Node105Step1Chunk3_2_checked, root7Node105Step1Chunk3_3_checked, root7Node105Step1Chunk3_4_checked, root7Node105Step1Chunk3_5_checked, root7Node105Step1Chunk4_0_checked, root7Node105Step1Chunk4_1_checked, root7Node105Step1Chunk4_2_checked, root7Node105Step1Chunk4_3_checked, root7Node105Step1Chunk4_4_checked, root7Node105Step1Chunk4_5_checked, root7Node105Step1Chunk5_0_checked, root7Node105Step1Chunk5_1_checked, root7Node105Step1Chunk5_2_checked, root7Node105Step1Chunk5_3_checked, root7Node105Step1Chunk5_4_checked, root7Node105Step1Chunk5_5_checked, root7Node105Step1Chunk6_0_checked, root7Node105Step1Chunk6_1_checked, root7Node105Step1Chunk6_2_checked, root7Node105Step1Chunk6_3_checked, root7Node105Step1Chunk6_4_checked, root7Node105Step1Chunk6_5_checked, root7Node105Step1Chunk7_0_checked, root7Node105Step1Chunk7_1_checked, root7Node105Step1Chunk7_2_checked, root7Node105Step1Chunk7_3_checked, root7Node105Step1Chunk7_4_checked, root7Node105Step1Chunk7_5_checked, root7Node105Step1Chunk8_0_checked, root7Node105Step1Chunk8_1_checked, root7Node105Step1Chunk8_2_checked, root7Node105Step1Chunk8_3_checked, root7Node105Step1Chunk8_4_checked, root7Node105Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node105Step1_checked :
    checkReplacement table57 root7Node105Domains0 root7Node105Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node105Domains0 root7Node105Domains1
    root7Node105Domains0Fast root7Node105Domains1Fast
    root7Node105Domains0_fast_eq root7Node105Domains1_fast_eq
    root7Node105Step1Narrowing_checked (by decide)
def root7Node105Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,2)]
  | 1 => [(7,4)]
  | 2 => [(1,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(5,5)]
  | 6 => [(1,1)]
  | 7 => [(8,1)]
  | 8 => [(6,5)]
  | 9 => [(0,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(3,0)]
  | 17 => [(2,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(4,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(5,1)]
  | 37 => [(0,1)]
  | 38 => [(6,2)]
  | 39 => [(8,4)]
  | 40 => [(8,0)]
  | 41 => [(7,3)]
  | 42 => [(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(8,5)]
  | 48 => [(1,0)]
  | 49 => [(7,1)]
  | 50 => [(1,5)]
  | 51 => [(6,4)]
  | 52 => [(1,2)]
  | 53 => [(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(0,3)]
  | 62 => [(8,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(8,1)]
  | 66 => [(6,5)]
  | 67 => [(0,4)]
  | 68 => [(5,4)]
  | 69 => [(0,0)]
  | 70 => [(5,3)]
  | 71 => [(5,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5)]
  | 75 => [(7,0)]
  | 76 => [(4,3)]
  | 77 => [(1,5)]
  | 78 => [(0,5)]
  | 79 => [(4,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(4,4)]
  | 83 => [(1,4)]
  | 84 => [(0,5)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(7,5)]
  | _ => [(6,0)]
def root7Node105Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,2)]
  | 1 => some [(7,4)]
  | 2 => some [(1,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(5,5)]
  | 6 => some [(1,1)]
  | 7 => some [(8,1)]
  | 8 => some [(6,5)]
  | 9 => some [(0,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(8,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(1,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(5,4)]
  | 69 => some [(0,0)]
  | 70 => some [(5,3)]
  | 71 => some [(5,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(7,0)]
  | 76 => some [(4,3)]
  | 77 => some [(1,5)]
  | 78 => some [(0,5)]
  | 79 => some [(4,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(1,4)]
  | 84 => some [(0,5)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(6,0)]
theorem root7Node105Domains2_fast_eq : root7Node105Domains2 = expandDomains root7Node105Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node105Domains2 v = expandDomains root7Node105Domains2Fast v from by decide) v
theorem root7Node105Step2Chunk0_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_0⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk0_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_1⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk0_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_2⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk0_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_3⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk0_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_4⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk0_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows0_5⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk1_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_0⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk1_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_1⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk1_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_2⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk1_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_3⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk1_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_4⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk1_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows1_5⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk2_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_0⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk2_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_1⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk2_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_2⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk2_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_3⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk2_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_4⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk2_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows2_5⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk3_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_0⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk3_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_1⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk3_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_2⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk3_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_3⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk3_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_4⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk3_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows3_5⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk4_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_0⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk4_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_1⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk4_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_2⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk4_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_3⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk4_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_4⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk4_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows4_5⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk5_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_0⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk5_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_1⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk5_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_2⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk5_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_3⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk5_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_4⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk5_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows5_5⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk6_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_0⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk6_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_1⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk6_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_2⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk6_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_3⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk6_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_4⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk6_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows6_5⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk7_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_0⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk7_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_1⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk7_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_2⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk7_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_3⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk7_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_4⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk7_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows7_5⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk8_0_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_0⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk8_1_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_1⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk8_2_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_2⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk8_3_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_3⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk8_4_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_4⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Chunk8_5_checked :
    checkNarrowing ⟨table52Scope, table52Rows8_5⟩
      root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq (by decide)
theorem root7Node105Step2Narrowing_checked :
    checkNarrowing table52 root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkNarrowing_flatten table52Scope [table52Rows0_0,table52Rows0_1,table52Rows0_2,table52Rows0_3,table52Rows0_4,table52Rows0_5,table52Rows1_0,table52Rows1_1,table52Rows1_2,table52Rows1_3,table52Rows1_4,table52Rows1_5,table52Rows2_0,table52Rows2_1,table52Rows2_2,table52Rows2_3,table52Rows2_4,table52Rows2_5,table52Rows3_0,table52Rows3_1,table52Rows3_2,table52Rows3_3,table52Rows3_4,table52Rows3_5,table52Rows4_0,table52Rows4_1,table52Rows4_2,table52Rows4_3,table52Rows4_4,table52Rows4_5,table52Rows5_0,table52Rows5_1,table52Rows5_2,table52Rows5_3,table52Rows5_4,table52Rows5_5,table52Rows6_0,table52Rows6_1,table52Rows6_2,table52Rows6_3,table52Rows6_4,table52Rows6_5,table52Rows7_0,table52Rows7_1,table52Rows7_2,table52Rows7_3,table52Rows7_4,table52Rows7_5,table52Rows8_0,table52Rows8_1,table52Rows8_2,table52Rows8_3,table52Rows8_4,table52Rows8_5]
    root7Node105Domains1 root7Node105Domains2 (by
      simp only [List.all_cons, List.all_nil, root7Node105Step2Chunk0_0_checked, root7Node105Step2Chunk0_1_checked, root7Node105Step2Chunk0_2_checked, root7Node105Step2Chunk0_3_checked, root7Node105Step2Chunk0_4_checked, root7Node105Step2Chunk0_5_checked, root7Node105Step2Chunk1_0_checked, root7Node105Step2Chunk1_1_checked, root7Node105Step2Chunk1_2_checked, root7Node105Step2Chunk1_3_checked, root7Node105Step2Chunk1_4_checked, root7Node105Step2Chunk1_5_checked, root7Node105Step2Chunk2_0_checked, root7Node105Step2Chunk2_1_checked, root7Node105Step2Chunk2_2_checked, root7Node105Step2Chunk2_3_checked, root7Node105Step2Chunk2_4_checked, root7Node105Step2Chunk2_5_checked, root7Node105Step2Chunk3_0_checked, root7Node105Step2Chunk3_1_checked, root7Node105Step2Chunk3_2_checked, root7Node105Step2Chunk3_3_checked, root7Node105Step2Chunk3_4_checked, root7Node105Step2Chunk3_5_checked, root7Node105Step2Chunk4_0_checked, root7Node105Step2Chunk4_1_checked, root7Node105Step2Chunk4_2_checked, root7Node105Step2Chunk4_3_checked, root7Node105Step2Chunk4_4_checked, root7Node105Step2Chunk4_5_checked, root7Node105Step2Chunk5_0_checked, root7Node105Step2Chunk5_1_checked, root7Node105Step2Chunk5_2_checked, root7Node105Step2Chunk5_3_checked, root7Node105Step2Chunk5_4_checked, root7Node105Step2Chunk5_5_checked, root7Node105Step2Chunk6_0_checked, root7Node105Step2Chunk6_1_checked, root7Node105Step2Chunk6_2_checked, root7Node105Step2Chunk6_3_checked, root7Node105Step2Chunk6_4_checked, root7Node105Step2Chunk6_5_checked, root7Node105Step2Chunk7_0_checked, root7Node105Step2Chunk7_1_checked, root7Node105Step2Chunk7_2_checked, root7Node105Step2Chunk7_3_checked, root7Node105Step2Chunk7_4_checked, root7Node105Step2Chunk7_5_checked, root7Node105Step2Chunk8_0_checked, root7Node105Step2Chunk8_1_checked, root7Node105Step2Chunk8_2_checked, root7Node105Step2Chunk8_3_checked, root7Node105Step2Chunk8_4_checked, root7Node105Step2Chunk8_5_checked, Bool.true_and])
theorem root7Node105Step2_checked :
    checkReplacement table52 root7Node105Domains1 root7Node105Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root7Node105Domains1 root7Node105Domains2
    root7Node105Domains1Fast root7Node105Domains2Fast
    root7Node105Domains1_fast_eq root7Node105Domains2_fast_eq
    root7Node105Step2Narrowing_checked (by decide)
theorem root7Node105Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node105Domains2 (.output 51) = true := by decide
def root7Node106Domains0 : Domains 91 State := restrict root7Node104Domains1 50 (7,5)
def root7Node106Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,2)]
  | 1 => some [(7,4)]
  | 2 => some [(1,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(5,5)]
  | 6 => some [(1,1)]
  | 7 => some [(8,1)]
  | 8 => some [(6,5)]
  | 9 => some [(0,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(8,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(1,0)]
  | 49 => some [(7,1)]
  | 50 => some [(7,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0),(8,0)]
  | 60 => some [(4,5),(7,3)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(5,4)]
  | 69 => some [(0,0),(6,4)]
  | 70 => some [(5,3)]
  | 71 => some [(5,5),(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5),(8,5)]
  | 75 => some [(7,0)]
  | 76 => some [(4,3)]
  | 77 => some [(1,5),(3,5),(7,5)]
  | 78 => some [(0,5),(6,3)]
  | 79 => some [(4,4),(7,2)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(6,3)]
  | 82 => some [(4,4),(7,2)]
  | 83 => some [(1,4),(7,4)]
  | 84 => some [(0,5),(6,3)]
  | 85 => some [(1,1),(7,1)]
  | 86 => some [(4,1),(7,5)]
  | 87 => some [(0,2),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(4,1),(7,5)]
  | _ => some [(0,2),(6,0)]
theorem root7Node106Domains0_fast_eq : root7Node106Domains0 = expandDomains root7Node106Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node106Domains0 v = expandDomains root7Node106Domains0Fast v from by decide) v
def root7Node106Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,2)]
  | 1 => [(7,4)]
  | 2 => [(1,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(5,5)]
  | 6 => [(1,1)]
  | 7 => [(8,1)]
  | 8 => [(6,5)]
  | 9 => [(0,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(3,0)]
  | 17 => [(2,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(4,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(5,1)]
  | 37 => [(0,1)]
  | 38 => [(6,2)]
  | 39 => [(8,4)]
  | 40 => [(8,0)]
  | 41 => [(7,3)]
  | 42 => [(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(8,5)]
  | 48 => [(1,0)]
  | 49 => [(7,1)]
  | 50 => [(7,5)]
  | 51 => [(6,4)]
  | 52 => [(1,2)]
  | 53 => [(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3)]
  | 58 => [(8,2)]
  | 59 => [(8,0)]
  | 60 => [(7,3)]
  | 61 => [(0,3)]
  | 62 => [(8,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(8,1)]
  | 66 => [(6,5)]
  | 67 => [(0,4)]
  | 68 => [(5,4)]
  | 69 => [(6,4)]
  | 70 => [(5,3)]
  | 71 => [(5,5),(8,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5),(8,5)]
  | 75 => [(7,0)]
  | 76 => [(4,3)]
  | 77 => [(3,5),(7,5)]
  | 78 => [(0,5),(6,3)]
  | 79 => [(4,4),(7,2)]
  | 80 => [(1,4),(7,4)]
  | 81 => [(0,5),(6,3)]
  | 82 => [(4,4),(7,2)]
  | 83 => [(1,4),(7,4)]
  | 84 => [(0,5),(6,3)]
  | 85 => [(1,1),(7,1)]
  | 86 => [(4,1),(7,5)]
  | 87 => [(0,2),(6,0)]
  | 88 => [(1,1),(7,1)]
  | 89 => [(4,1),(7,5)]
  | _ => [(0,2),(6,0)]
def root7Node106Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,2)]
  | 1 => some [(7,4)]
  | 2 => some [(1,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(5,5)]
  | 6 => some [(1,1)]
  | 7 => some [(8,1)]
  | 8 => some [(6,5)]
  | 9 => some [(0,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(3,0)]
  | 17 => some [(2,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(8,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(1,0)]
  | 49 => some [(7,1)]
  | 50 => some [(7,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(8,2)]
  | 59 => some [(8,0)]
  | 60 => some [(7,3)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(5,4)]
  | 69 => some [(6,4)]
  | 70 => some [(5,3)]
  | 71 => some [(5,5),(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5),(8,5)]
  | 75 => some [(7,0)]
  | 76 => some [(4,3)]
  | 77 => some [(3,5),(7,5)]
  | 78 => some [(0,5),(6,3)]
  | 79 => some [(4,4),(7,2)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(6,3)]
  | 82 => some [(4,4),(7,2)]
  | 83 => some [(1,4),(7,4)]
  | 84 => some [(0,5),(6,3)]
  | 85 => some [(1,1),(7,1)]
  | 86 => some [(4,1),(7,5)]
  | 87 => some [(0,2),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(4,1),(7,5)]
  | _ => some [(0,2),(6,0)]
theorem root7Node106Domains1_fast_eq : root7Node106Domains1 = expandDomains root7Node106Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node106Domains1 v = expandDomains root7Node106Domains1Fast v from by decide) v
theorem root7Node106Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq (by decide)
theorem root7Node106Step1Narrowing_checked :
    checkNarrowing table36 root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root7Node106Domains0 root7Node106Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node106Step1Chunk0_0_checked, root7Node106Step1Chunk0_1_checked, root7Node106Step1Chunk0_2_checked, root7Node106Step1Chunk0_3_checked, root7Node106Step1Chunk0_4_checked, root7Node106Step1Chunk0_5_checked, root7Node106Step1Chunk1_0_checked, root7Node106Step1Chunk1_1_checked, root7Node106Step1Chunk1_2_checked, root7Node106Step1Chunk1_3_checked, root7Node106Step1Chunk1_4_checked, root7Node106Step1Chunk1_5_checked, root7Node106Step1Chunk2_0_checked, root7Node106Step1Chunk2_1_checked, root7Node106Step1Chunk2_2_checked, root7Node106Step1Chunk2_3_checked, root7Node106Step1Chunk2_4_checked, root7Node106Step1Chunk2_5_checked, root7Node106Step1Chunk3_0_checked, root7Node106Step1Chunk3_1_checked, root7Node106Step1Chunk3_2_checked, root7Node106Step1Chunk3_3_checked, root7Node106Step1Chunk3_4_checked, root7Node106Step1Chunk3_5_checked, root7Node106Step1Chunk4_0_checked, root7Node106Step1Chunk4_1_checked, root7Node106Step1Chunk4_2_checked, root7Node106Step1Chunk4_3_checked, root7Node106Step1Chunk4_4_checked, root7Node106Step1Chunk4_5_checked, root7Node106Step1Chunk5_0_checked, root7Node106Step1Chunk5_1_checked, root7Node106Step1Chunk5_2_checked, root7Node106Step1Chunk5_3_checked, root7Node106Step1Chunk5_4_checked, root7Node106Step1Chunk5_5_checked, root7Node106Step1Chunk6_0_checked, root7Node106Step1Chunk6_1_checked, root7Node106Step1Chunk6_2_checked, root7Node106Step1Chunk6_3_checked, root7Node106Step1Chunk6_4_checked, root7Node106Step1Chunk6_5_checked, root7Node106Step1Chunk7_0_checked, root7Node106Step1Chunk7_1_checked, root7Node106Step1Chunk7_2_checked, root7Node106Step1Chunk7_3_checked, root7Node106Step1Chunk7_4_checked, root7Node106Step1Chunk7_5_checked, root7Node106Step1Chunk8_0_checked, root7Node106Step1Chunk8_1_checked, root7Node106Step1Chunk8_2_checked, root7Node106Step1Chunk8_3_checked, root7Node106Step1Chunk8_4_checked, root7Node106Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node106Step1_checked :
    checkReplacement table36 root7Node106Domains0 root7Node106Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node106Domains0 root7Node106Domains1
    root7Node106Domains0Fast root7Node106Domains1Fast
    root7Node106Domains0_fast_eq root7Node106Domains1_fast_eq
    root7Node106Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
