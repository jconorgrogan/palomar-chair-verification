module

public import SpectreFinite.RadiusFiveRoot7Part69
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable3
public import SpectreFinite.RadiusFiveTable32
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node179Domains0 : Domains 91 State := restrict root7Node178Domains3 0 (2,4)
def root7Node179Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2),(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3),(8,3)]
  | 5 => some [(4,2),(5,2),(5,5),(8,2)]
  | 6 => some [(7,1),(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(1,4),(6,4)]
  | 11 => some [(0,5),(1,2)]
  | 12 => some [(4,4),(7,4),(8,4)]
  | 13 => some [(5,0),(5,3),(8,3)]
  | 14 => some [(4,5),(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3),(6,0)]
  | 19 => some [(7,1),(8,1)]
  | 20 => some [(1,5),(6,5),(7,5)]
  | 21 => some [(7,4),(8,4)]
  | 22 => some [(0,0),(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2),(8,2)]
  | 27 => some [(5,0),(5,3),(8,0)]
  | 28 => some [(4,5),(7,3),(8,5)]
  | 29 => some [(4,2),(7,0),(8,2)]
  | 30 => some [(4,1),(7,1),(8,1)]
  | 31 => some [(0,2),(1,5)]
  | 32 => some [(1,1),(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(3,4),(5,4)]
  | 37 => some [(0,0),(6,3),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4),(8,4)]
  | 40 => some [(1,3),(3,3),(5,0),(5,3),(7,3)]
  | 41 => some [(4,5),(5,2),(5,5),(8,5)]
  | 42 => some [(7,0),(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(2,3),(4,3)]
  | 47 => some [(0,2),(1,5),(3,5),(7,5)]
  | 48 => some [(0,3),(1,1),(6,1)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(1,5),(6,5)]
  | 51 => some [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 52 => some [(4,4),(5,4),(7,2),(8,4)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(6,4),(7,4)]
  | 57 => some [(0,5),(1,2),(1,3),(6,3)]
  | 58 => some [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 59 => some [(1,3),(3,3),(5,3),(7,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(1,1),(4,3),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(1,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(0,3),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => some [(0,1),(1,4),(3,4),(6,5)]
  | 69 => some [(0,4),(0,5),(6,2),(6,3)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(5,2),(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(4,2),(5,2),(5,5),(8,2)]
  | 75 => some [(3,0),(5,0),(5,3),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5),(8,5)]
  | 77 => some [(0,2),(1,0),(6,0),(7,0)]
  | 78 => some [(0,4),(6,2)]
  | 79 => some [(5,4),(8,4)]
  | 80 => some [(1,4),(6,4)]
  | 81 => some [(0,5),(1,2)]
  | 82 => some [(4,4),(7,4),(8,4)]
  | 83 => some [(0,0),(1,3),(6,3),(6,4)]
  | 84 => some [(1,2),(7,2),(8,2)]
  | 85 => some [(4,3),(7,1)]
  | 86 => some [(3,5),(7,5)]
  | 87 => some [(0,3),(6,0)]
  | 88 => some [(4,1),(7,1),(8,1)]
  | 89 => some [(0,2),(1,5),(6,5),(7,5)]
  | _ => some [(0,3),(0,4),(1,1),(6,1)]
theorem root7Node179Domains0_fast_eq : root7Node179Domains0 = expandDomains root7Node179Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node179Domains0 v = expandDomains root7Node179Domains0Fast v from by decide) v
def root7Node179Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4)]
  | 1 => [(1,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3),(8,3)]
  | 5 => [(4,2),(5,2),(5,5),(8,2)]
  | 6 => [(7,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(1,4),(6,4)]
  | 11 => [(0,5),(1,2)]
  | 12 => [(4,4),(7,4),(8,4)]
  | 13 => [(5,0)]
  | 14 => [(4,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(0,3),(6,0)]
  | 19 => [(7,1),(8,1)]
  | 20 => [(1,5),(6,5),(7,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(4,2),(8,2)]
  | 27 => [(5,0),(5,3),(8,0)]
  | 28 => [(4,5),(7,3),(8,5)]
  | 29 => [(4,2),(7,0),(8,2)]
  | 30 => [(7,1),(8,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(3,4),(5,4)]
  | 37 => [(0,0),(6,3),(6,4)]
  | 38 => [(1,2),(7,2)]
  | 39 => [(7,4),(8,4)]
  | 40 => [(5,0),(5,3)]
  | 41 => [(4,5),(5,5),(8,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(2,3),(4,3)]
  | 47 => [(0,2),(1,5),(3,5),(7,5)]
  | 48 => [(0,3),(1,1),(6,1)]
  | 49 => [(4,1),(8,1)]
  | 50 => [(0,2),(1,5),(6,5)]
  | 51 => [(0,0),(0,5),(6,3)]
  | 52 => [(4,4),(7,2)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(6,4),(7,4)]
  | 57 => [(0,5),(1,2),(1,3),(6,3)]
  | 58 => [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 59 => [(1,3),(3,3),(5,3),(7,3)]
  | 60 => [(5,2),(5,5),(8,5)]
  | 61 => [(1,1),(6,1),(7,1)]
  | 62 => [(4,1),(7,5)]
  | 63 => [(0,2),(6,0)]
  | 64 => [(1,1),(7,1)]
  | 65 => [(4,1),(7,5),(8,1)]
  | 66 => [(0,2),(0,3),(6,0),(6,5)]
  | 67 => [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => [(0,1),(1,4),(3,4),(6,5)]
  | 69 => [(0,4),(0,5),(6,2),(6,3)]
  | 70 => [(7,3)]
  | 71 => [(5,2),(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(4,2),(5,2),(5,5),(8,2)]
  | 75 => [(3,0),(5,0),(5,3),(7,0)]
  | 76 => [(2,3),(2,5),(4,5),(8,5)]
  | 77 => [(0,2),(1,0),(6,0),(7,0)]
  | 78 => [(0,4),(6,2)]
  | 79 => [(5,4),(8,4)]
  | 80 => [(1,4),(6,4)]
  | 81 => [(0,5),(1,2)]
  | 82 => [(4,4),(7,4),(8,4)]
  | 83 => [(0,0),(1,3),(6,3),(6,4)]
  | 84 => [(1,2),(7,2),(8,2)]
  | 85 => [(4,3),(7,1)]
  | 86 => [(3,5),(7,5)]
  | 87 => [(0,3),(6,0)]
  | 88 => [(4,1),(7,1),(8,1)]
  | 89 => [(0,2),(1,5),(6,5),(7,5)]
  | _ => [(0,3),(0,4),(1,1),(6,1)]
def root7Node179Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3),(8,3)]
  | 5 => some [(4,2),(5,2),(5,5),(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(1,4),(6,4)]
  | 11 => some [(0,5),(1,2)]
  | 12 => some [(4,4),(7,4),(8,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3),(6,0)]
  | 19 => some [(7,1),(8,1)]
  | 20 => some [(1,5),(6,5),(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2),(8,2)]
  | 27 => some [(5,0),(5,3),(8,0)]
  | 28 => some [(4,5),(7,3),(8,5)]
  | 29 => some [(4,2),(7,0),(8,2)]
  | 30 => some [(7,1),(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(3,4),(5,4)]
  | 37 => some [(0,0),(6,3),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4),(8,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(5,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(2,3),(4,3)]
  | 47 => some [(0,2),(1,5),(3,5),(7,5)]
  | 48 => some [(0,3),(1,1),(6,1)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(1,5),(6,5)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(6,4),(7,4)]
  | 57 => some [(0,5),(1,2),(1,3),(6,3)]
  | 58 => some [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 59 => some [(1,3),(3,3),(5,3),(7,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(1,1),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(1,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(0,3),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => some [(0,1),(1,4),(3,4),(6,5)]
  | 69 => some [(0,4),(0,5),(6,2),(6,3)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2),(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(4,2),(5,2),(5,5),(8,2)]
  | 75 => some [(3,0),(5,0),(5,3),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5),(8,5)]
  | 77 => some [(0,2),(1,0),(6,0),(7,0)]
  | 78 => some [(0,4),(6,2)]
  | 79 => some [(5,4),(8,4)]
  | 80 => some [(1,4),(6,4)]
  | 81 => some [(0,5),(1,2)]
  | 82 => some [(4,4),(7,4),(8,4)]
  | 83 => some [(0,0),(1,3),(6,3),(6,4)]
  | 84 => some [(1,2),(7,2),(8,2)]
  | 85 => some [(4,3),(7,1)]
  | 86 => some [(3,5),(7,5)]
  | 87 => some [(0,3),(6,0)]
  | 88 => some [(4,1),(7,1),(8,1)]
  | 89 => some [(0,2),(1,5),(6,5),(7,5)]
  | _ => some [(0,3),(0,4),(1,1),(6,1)]
theorem root7Node179Domains1_fast_eq : root7Node179Domains1 = expandDomains root7Node179Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node179Domains1 v = expandDomains root7Node179Domains1Fast v from by decide) v
theorem root7Node179Step1Chunk0_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows0_0⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk0_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows0_1⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk0_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows0_2⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk0_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows0_3⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk0_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows0_4⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk0_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows0_5⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk1_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows1_0⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk1_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows1_1⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk1_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows1_2⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk1_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows1_3⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk1_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows1_4⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk1_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows1_5⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk2_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows2_0⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk2_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows2_1⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk2_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows2_2⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk2_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows2_3⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk2_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows2_4⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk2_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows2_5⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk3_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows3_0⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk3_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows3_1⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk3_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows3_2⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk3_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows3_3⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk3_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows3_4⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk3_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows3_5⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk4_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows4_0⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk4_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows4_1⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk4_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows4_2⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk4_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows4_3⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk4_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows4_4⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk4_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows4_5⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk5_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows5_0⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk5_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows5_1⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk5_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows5_2⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk5_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows5_3⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk5_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows5_4⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk5_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows5_5⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk6_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows6_0⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk6_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows6_1⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk6_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows6_2⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk6_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows6_3⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk6_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows6_4⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk6_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows6_5⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk7_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows7_0⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk7_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows7_1⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk7_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows7_2⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk7_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows7_3⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk7_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows7_4⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk7_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows7_5⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk8_0_checked :
    checkNarrowing ⟨table32Scope, table32Rows8_0⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk8_1_checked :
    checkNarrowing ⟨table32Scope, table32Rows8_1⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk8_2_checked :
    checkNarrowing ⟨table32Scope, table32Rows8_2⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk8_3_checked :
    checkNarrowing ⟨table32Scope, table32Rows8_3⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk8_4_checked :
    checkNarrowing ⟨table32Scope, table32Rows8_4⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Chunk8_5_checked :
    checkNarrowing ⟨table32Scope, table32Rows8_5⟩
      root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq (by decide)
theorem root7Node179Step1Narrowing_checked :
    checkNarrowing table32 root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkNarrowing_flatten table32Scope [table32Rows0_0,table32Rows0_1,table32Rows0_2,table32Rows0_3,table32Rows0_4,table32Rows0_5,table32Rows1_0,table32Rows1_1,table32Rows1_2,table32Rows1_3,table32Rows1_4,table32Rows1_5,table32Rows2_0,table32Rows2_1,table32Rows2_2,table32Rows2_3,table32Rows2_4,table32Rows2_5,table32Rows3_0,table32Rows3_1,table32Rows3_2,table32Rows3_3,table32Rows3_4,table32Rows3_5,table32Rows4_0,table32Rows4_1,table32Rows4_2,table32Rows4_3,table32Rows4_4,table32Rows4_5,table32Rows5_0,table32Rows5_1,table32Rows5_2,table32Rows5_3,table32Rows5_4,table32Rows5_5,table32Rows6_0,table32Rows6_1,table32Rows6_2,table32Rows6_3,table32Rows6_4,table32Rows6_5,table32Rows7_0,table32Rows7_1,table32Rows7_2,table32Rows7_3,table32Rows7_4,table32Rows7_5,table32Rows8_0,table32Rows8_1,table32Rows8_2,table32Rows8_3,table32Rows8_4,table32Rows8_5]
    root7Node179Domains0 root7Node179Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node179Step1Chunk0_0_checked, root7Node179Step1Chunk0_1_checked, root7Node179Step1Chunk0_2_checked, root7Node179Step1Chunk0_3_checked, root7Node179Step1Chunk0_4_checked, root7Node179Step1Chunk0_5_checked, root7Node179Step1Chunk1_0_checked, root7Node179Step1Chunk1_1_checked, root7Node179Step1Chunk1_2_checked, root7Node179Step1Chunk1_3_checked, root7Node179Step1Chunk1_4_checked, root7Node179Step1Chunk1_5_checked, root7Node179Step1Chunk2_0_checked, root7Node179Step1Chunk2_1_checked, root7Node179Step1Chunk2_2_checked, root7Node179Step1Chunk2_3_checked, root7Node179Step1Chunk2_4_checked, root7Node179Step1Chunk2_5_checked, root7Node179Step1Chunk3_0_checked, root7Node179Step1Chunk3_1_checked, root7Node179Step1Chunk3_2_checked, root7Node179Step1Chunk3_3_checked, root7Node179Step1Chunk3_4_checked, root7Node179Step1Chunk3_5_checked, root7Node179Step1Chunk4_0_checked, root7Node179Step1Chunk4_1_checked, root7Node179Step1Chunk4_2_checked, root7Node179Step1Chunk4_3_checked, root7Node179Step1Chunk4_4_checked, root7Node179Step1Chunk4_5_checked, root7Node179Step1Chunk5_0_checked, root7Node179Step1Chunk5_1_checked, root7Node179Step1Chunk5_2_checked, root7Node179Step1Chunk5_3_checked, root7Node179Step1Chunk5_4_checked, root7Node179Step1Chunk5_5_checked, root7Node179Step1Chunk6_0_checked, root7Node179Step1Chunk6_1_checked, root7Node179Step1Chunk6_2_checked, root7Node179Step1Chunk6_3_checked, root7Node179Step1Chunk6_4_checked, root7Node179Step1Chunk6_5_checked, root7Node179Step1Chunk7_0_checked, root7Node179Step1Chunk7_1_checked, root7Node179Step1Chunk7_2_checked, root7Node179Step1Chunk7_3_checked, root7Node179Step1Chunk7_4_checked, root7Node179Step1Chunk7_5_checked, root7Node179Step1Chunk8_0_checked, root7Node179Step1Chunk8_1_checked, root7Node179Step1Chunk8_2_checked, root7Node179Step1Chunk8_3_checked, root7Node179Step1Chunk8_4_checked, root7Node179Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node179Step1_checked :
    checkReplacement table32 root7Node179Domains0 root7Node179Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node179Domains0 root7Node179Domains1
    root7Node179Domains0Fast root7Node179Domains1Fast
    root7Node179Domains0_fast_eq root7Node179Domains1_fast_eq
    root7Node179Step1Narrowing_checked (by decide)
def root7Node179Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4)]
  | 1 => [(1,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3),(8,3)]
  | 5 => [(4,2),(5,2),(5,5),(8,2)]
  | 6 => [(7,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(1,4),(6,4)]
  | 11 => [(0,5),(1,2)]
  | 12 => [(4,4),(7,4),(8,4)]
  | 13 => [(5,0)]
  | 14 => [(4,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(0,3),(6,0)]
  | 19 => [(7,1),(8,1)]
  | 20 => [(1,5),(6,5),(7,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(4,2),(8,2)]
  | 27 => [(5,0),(5,3),(8,0)]
  | 28 => [(4,5),(7,3),(8,5)]
  | 29 => [(4,2),(7,0),(8,2)]
  | 30 => [(7,1),(8,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(3,4),(5,4)]
  | 37 => [(0,0),(6,3),(6,4)]
  | 38 => [(1,2),(7,2)]
  | 39 => [(7,4),(8,4)]
  | 40 => [(5,0),(5,3)]
  | 41 => [(4,5),(5,5),(8,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(2,3),(4,3)]
  | 47 => [(0,2),(1,5),(3,5),(7,5)]
  | 48 => [(0,3),(1,1),(6,1)]
  | 49 => [(4,1),(8,1)]
  | 50 => [(0,2),(1,5),(6,5)]
  | 51 => [(0,0),(0,5),(6,3)]
  | 52 => [(4,4),(7,2)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(6,4),(7,4)]
  | 57 => [(0,5),(1,2),(1,3),(6,3)]
  | 58 => [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 59 => [(1,3),(3,3),(5,3),(7,3)]
  | 60 => [(5,2),(5,5),(8,5)]
  | 61 => [(1,1),(6,1),(7,1)]
  | 62 => [(4,1),(7,5)]
  | 63 => [(0,2),(6,0)]
  | 64 => [(1,1),(7,1)]
  | 65 => [(4,1),(7,5),(8,1)]
  | 66 => [(0,2),(0,3),(6,0),(6,5)]
  | 67 => [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => [(0,1),(1,4),(3,4),(6,5)]
  | 69 => [(0,4),(0,5),(6,2),(6,3)]
  | 70 => [(7,3)]
  | 71 => [(5,2),(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(4,2),(5,2),(5,5),(8,2)]
  | 75 => [(3,0),(5,0),(5,3),(7,0)]
  | 76 => [(2,3),(2,5),(4,5),(8,5)]
  | 77 => [(0,2),(1,0),(6,0),(7,0)]
  | 78 => [(6,2)]
  | 79 => [(8,4)]
  | 80 => [(1,4),(6,4)]
  | 81 => [(0,5),(1,2)]
  | 82 => [(4,4),(7,4),(8,4)]
  | 83 => [(0,0),(1,3),(6,4)]
  | 84 => [(1,2),(7,2),(8,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(0,3),(6,0)]
  | 88 => [(7,1),(8,1)]
  | 89 => [(1,5),(6,5),(7,5)]
  | _ => [(0,3),(0,4),(6,1)]
def root7Node179Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3),(8,3)]
  | 5 => some [(4,2),(5,2),(5,5),(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(1,4),(6,4)]
  | 11 => some [(0,5),(1,2)]
  | 12 => some [(4,4),(7,4),(8,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3),(6,0)]
  | 19 => some [(7,1),(8,1)]
  | 20 => some [(1,5),(6,5),(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2),(8,2)]
  | 27 => some [(5,0),(5,3),(8,0)]
  | 28 => some [(4,5),(7,3),(8,5)]
  | 29 => some [(4,2),(7,0),(8,2)]
  | 30 => some [(7,1),(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(3,4),(5,4)]
  | 37 => some [(0,0),(6,3),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4),(8,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(5,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(2,3),(4,3)]
  | 47 => some [(0,2),(1,5),(3,5),(7,5)]
  | 48 => some [(0,3),(1,1),(6,1)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(1,5),(6,5)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(6,4),(7,4)]
  | 57 => some [(0,5),(1,2),(1,3),(6,3)]
  | 58 => some [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 59 => some [(1,3),(3,3),(5,3),(7,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(1,1),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(1,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(0,3),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => some [(0,1),(1,4),(3,4),(6,5)]
  | 69 => some [(0,4),(0,5),(6,2),(6,3)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2),(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(4,2),(5,2),(5,5),(8,2)]
  | 75 => some [(3,0),(5,0),(5,3),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5),(8,5)]
  | 77 => some [(0,2),(1,0),(6,0),(7,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(1,4),(6,4)]
  | 81 => some [(0,5),(1,2)]
  | 82 => some [(4,4),(7,4),(8,4)]
  | 83 => some [(0,0),(1,3),(6,4)]
  | 84 => some [(1,2),(7,2),(8,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3),(6,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5),(6,5),(7,5)]
  | _ => some [(0,3),(0,4),(6,1)]
theorem root7Node179Domains2_fast_eq : root7Node179Domains2 = expandDomains root7Node179Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node179Domains2 v = expandDomains root7Node179Domains2Fast v from by decide) v
theorem root7Node179Step2Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq (by decide)
theorem root7Node179Step2Narrowing_checked :
    checkNarrowing table65 root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root7Node179Domains1 root7Node179Domains2 (by
      simp only [List.all_cons, List.all_nil, root7Node179Step2Chunk0_0_checked, root7Node179Step2Chunk0_1_checked, root7Node179Step2Chunk0_2_checked, root7Node179Step2Chunk0_3_checked, root7Node179Step2Chunk0_4_checked, root7Node179Step2Chunk0_5_checked, root7Node179Step2Chunk1_0_checked, root7Node179Step2Chunk1_1_checked, root7Node179Step2Chunk1_2_checked, root7Node179Step2Chunk1_3_checked, root7Node179Step2Chunk1_4_checked, root7Node179Step2Chunk1_5_checked, root7Node179Step2Chunk2_0_checked, root7Node179Step2Chunk2_1_checked, root7Node179Step2Chunk2_2_checked, root7Node179Step2Chunk2_3_checked, root7Node179Step2Chunk2_4_checked, root7Node179Step2Chunk2_5_checked, root7Node179Step2Chunk3_0_checked, root7Node179Step2Chunk3_1_checked, root7Node179Step2Chunk3_2_checked, root7Node179Step2Chunk3_3_checked, root7Node179Step2Chunk3_4_checked, root7Node179Step2Chunk3_5_checked, root7Node179Step2Chunk4_0_checked, root7Node179Step2Chunk4_1_checked, root7Node179Step2Chunk4_2_checked, root7Node179Step2Chunk4_3_checked, root7Node179Step2Chunk4_4_checked, root7Node179Step2Chunk4_5_checked, root7Node179Step2Chunk5_0_checked, root7Node179Step2Chunk5_1_checked, root7Node179Step2Chunk5_2_checked, root7Node179Step2Chunk5_3_checked, root7Node179Step2Chunk5_4_checked, root7Node179Step2Chunk5_5_checked, root7Node179Step2Chunk6_0_checked, root7Node179Step2Chunk6_1_checked, root7Node179Step2Chunk6_2_checked, root7Node179Step2Chunk6_3_checked, root7Node179Step2Chunk6_4_checked, root7Node179Step2Chunk6_5_checked, root7Node179Step2Chunk7_0_checked, root7Node179Step2Chunk7_1_checked, root7Node179Step2Chunk7_2_checked, root7Node179Step2Chunk7_3_checked, root7Node179Step2Chunk7_4_checked, root7Node179Step2Chunk7_5_checked, root7Node179Step2Chunk8_0_checked, root7Node179Step2Chunk8_1_checked, root7Node179Step2Chunk8_2_checked, root7Node179Step2Chunk8_3_checked, root7Node179Step2Chunk8_4_checked, root7Node179Step2Chunk8_5_checked, Bool.true_and])
theorem root7Node179Step2_checked :
    checkReplacement table65 root7Node179Domains1 root7Node179Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root7Node179Domains1 root7Node179Domains2
    root7Node179Domains1Fast root7Node179Domains2Fast
    root7Node179Domains1_fast_eq root7Node179Domains2_fast_eq
    root7Node179Step2Narrowing_checked (by decide)
def root7Node179Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4)]
  | 1 => [(1,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3),(8,3)]
  | 5 => [(5,2),(5,5)]
  | 6 => [(7,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(1,4),(6,4)]
  | 11 => [(0,5),(1,2)]
  | 12 => [(4,4),(8,4)]
  | 13 => [(5,0)]
  | 14 => [(4,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(0,3),(6,0)]
  | 19 => [(7,1),(8,1)]
  | 20 => [(1,5),(7,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(4,2),(8,2)]
  | 27 => [(5,0),(5,3),(8,0)]
  | 28 => [(4,5),(7,3),(8,5)]
  | 29 => [(4,2),(7,0),(8,2)]
  | 30 => [(7,1),(8,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(3,4),(5,4)]
  | 37 => [(0,0),(6,3),(6,4)]
  | 38 => [(1,2),(7,2)]
  | 39 => [(7,4),(8,4)]
  | 40 => [(5,0),(5,3)]
  | 41 => [(4,5),(5,5),(8,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(2,3),(4,3)]
  | 47 => [(0,2),(1,5),(3,5),(7,5)]
  | 48 => [(0,3),(1,1),(6,1)]
  | 49 => [(4,1),(8,1)]
  | 50 => [(0,2),(1,5),(6,5)]
  | 51 => [(0,0),(0,5),(6,3)]
  | 52 => [(4,4),(7,2)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(6,4),(7,4)]
  | 57 => [(0,5),(1,2),(1,3),(6,3)]
  | 58 => [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 59 => [(1,3),(3,3),(5,3),(7,3)]
  | 60 => [(5,2),(5,5),(8,5)]
  | 61 => [(1,1),(6,1),(7,1)]
  | 62 => [(4,1),(7,5)]
  | 63 => [(0,2),(6,0)]
  | 64 => [(1,1),(7,1)]
  | 65 => [(4,1),(7,5),(8,1)]
  | 66 => [(0,2),(0,3),(6,0),(6,5)]
  | 67 => [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => [(0,1),(1,4),(3,4),(6,5)]
  | 69 => [(0,4),(0,5),(6,2),(6,3)]
  | 70 => [(7,3)]
  | 71 => [(5,2),(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(4,2),(5,2),(5,5),(8,2)]
  | 75 => [(3,0),(5,0),(5,3),(7,0)]
  | 76 => [(2,3),(2,5),(4,5),(8,5)]
  | 77 => [(0,2),(1,0),(6,0),(7,0)]
  | 78 => [(6,2)]
  | 79 => [(8,4)]
  | 80 => [(1,4),(6,4)]
  | 81 => [(0,5),(1,2)]
  | 82 => [(4,4),(7,4),(8,4)]
  | 83 => [(0,0),(1,3),(6,4)]
  | 84 => [(1,2),(7,2),(8,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(0,3),(6,0)]
  | 88 => [(7,1),(8,1)]
  | 89 => [(1,5),(6,5),(7,5)]
  | _ => [(0,3),(0,4),(6,1)]
def root7Node179Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3),(8,3)]
  | 5 => some [(5,2),(5,5)]
  | 6 => some [(7,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(1,4),(6,4)]
  | 11 => some [(0,5),(1,2)]
  | 12 => some [(4,4),(8,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3),(6,0)]
  | 19 => some [(7,1),(8,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2),(8,2)]
  | 27 => some [(5,0),(5,3),(8,0)]
  | 28 => some [(4,5),(7,3),(8,5)]
  | 29 => some [(4,2),(7,0),(8,2)]
  | 30 => some [(7,1),(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(3,4),(5,4)]
  | 37 => some [(0,0),(6,3),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4),(8,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(5,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(2,3),(4,3)]
  | 47 => some [(0,2),(1,5),(3,5),(7,5)]
  | 48 => some [(0,3),(1,1),(6,1)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(1,5),(6,5)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(6,4),(7,4)]
  | 57 => some [(0,5),(1,2),(1,3),(6,3)]
  | 58 => some [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 59 => some [(1,3),(3,3),(5,3),(7,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(1,1),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(1,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(0,3),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => some [(0,1),(1,4),(3,4),(6,5)]
  | 69 => some [(0,4),(0,5),(6,2),(6,3)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2),(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(4,2),(5,2),(5,5),(8,2)]
  | 75 => some [(3,0),(5,0),(5,3),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5),(8,5)]
  | 77 => some [(0,2),(1,0),(6,0),(7,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(1,4),(6,4)]
  | 81 => some [(0,5),(1,2)]
  | 82 => some [(4,4),(7,4),(8,4)]
  | 83 => some [(0,0),(1,3),(6,4)]
  | 84 => some [(1,2),(7,2),(8,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3),(6,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5),(6,5),(7,5)]
  | _ => some [(0,3),(0,4),(6,1)]
theorem root7Node179Domains3_fast_eq : root7Node179Domains3 = expandDomains root7Node179Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node179Domains3 v = expandDomains root7Node179Domains3Fast v from by decide) v
theorem root7Node179Step3Chunk0_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_0⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk0_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_1⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk0_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_2⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk0_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_3⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk0_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_4⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk0_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_5⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk1_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_0⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk1_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_1⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk1_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_2⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk1_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_3⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk1_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_4⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk1_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_5⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk2_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_0⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk2_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_1⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk2_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_2⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk2_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_3⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk2_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_4⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk2_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_5⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk3_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_0⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk3_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_1⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk3_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_2⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk3_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_3⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk3_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_4⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk3_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_5⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk4_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_0⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk4_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_1⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk4_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_2⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk4_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_3⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk4_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_4⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk4_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_5⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk5_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_0⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk5_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_1⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk5_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_2⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk5_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_3⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk5_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_4⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk5_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_5⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk6_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_0⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk6_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_1⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk6_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_2⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk6_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_3⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk6_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_4⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk6_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_5⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk7_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_0⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk7_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_1⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk7_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_2⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk7_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_3⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk7_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_4⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk7_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_5⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk8_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_0⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk8_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_1⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk8_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_2⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk8_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_3⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk8_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_4⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Chunk8_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_5⟩
      root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq (by decide)
theorem root7Node179Step3Narrowing_checked :
    checkNarrowing table3 root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkNarrowing_flatten table3Scope [table3Rows0_0,table3Rows0_1,table3Rows0_2,table3Rows0_3,table3Rows0_4,table3Rows0_5,table3Rows1_0,table3Rows1_1,table3Rows1_2,table3Rows1_3,table3Rows1_4,table3Rows1_5,table3Rows2_0,table3Rows2_1,table3Rows2_2,table3Rows2_3,table3Rows2_4,table3Rows2_5,table3Rows3_0,table3Rows3_1,table3Rows3_2,table3Rows3_3,table3Rows3_4,table3Rows3_5,table3Rows4_0,table3Rows4_1,table3Rows4_2,table3Rows4_3,table3Rows4_4,table3Rows4_5,table3Rows5_0,table3Rows5_1,table3Rows5_2,table3Rows5_3,table3Rows5_4,table3Rows5_5,table3Rows6_0,table3Rows6_1,table3Rows6_2,table3Rows6_3,table3Rows6_4,table3Rows6_5,table3Rows7_0,table3Rows7_1,table3Rows7_2,table3Rows7_3,table3Rows7_4,table3Rows7_5,table3Rows8_0,table3Rows8_1,table3Rows8_2,table3Rows8_3,table3Rows8_4,table3Rows8_5]
    root7Node179Domains2 root7Node179Domains3 (by
      simp only [List.all_cons, List.all_nil, root7Node179Step3Chunk0_0_checked, root7Node179Step3Chunk0_1_checked, root7Node179Step3Chunk0_2_checked, root7Node179Step3Chunk0_3_checked, root7Node179Step3Chunk0_4_checked, root7Node179Step3Chunk0_5_checked, root7Node179Step3Chunk1_0_checked, root7Node179Step3Chunk1_1_checked, root7Node179Step3Chunk1_2_checked, root7Node179Step3Chunk1_3_checked, root7Node179Step3Chunk1_4_checked, root7Node179Step3Chunk1_5_checked, root7Node179Step3Chunk2_0_checked, root7Node179Step3Chunk2_1_checked, root7Node179Step3Chunk2_2_checked, root7Node179Step3Chunk2_3_checked, root7Node179Step3Chunk2_4_checked, root7Node179Step3Chunk2_5_checked, root7Node179Step3Chunk3_0_checked, root7Node179Step3Chunk3_1_checked, root7Node179Step3Chunk3_2_checked, root7Node179Step3Chunk3_3_checked, root7Node179Step3Chunk3_4_checked, root7Node179Step3Chunk3_5_checked, root7Node179Step3Chunk4_0_checked, root7Node179Step3Chunk4_1_checked, root7Node179Step3Chunk4_2_checked, root7Node179Step3Chunk4_3_checked, root7Node179Step3Chunk4_4_checked, root7Node179Step3Chunk4_5_checked, root7Node179Step3Chunk5_0_checked, root7Node179Step3Chunk5_1_checked, root7Node179Step3Chunk5_2_checked, root7Node179Step3Chunk5_3_checked, root7Node179Step3Chunk5_4_checked, root7Node179Step3Chunk5_5_checked, root7Node179Step3Chunk6_0_checked, root7Node179Step3Chunk6_1_checked, root7Node179Step3Chunk6_2_checked, root7Node179Step3Chunk6_3_checked, root7Node179Step3Chunk6_4_checked, root7Node179Step3Chunk6_5_checked, root7Node179Step3Chunk7_0_checked, root7Node179Step3Chunk7_1_checked, root7Node179Step3Chunk7_2_checked, root7Node179Step3Chunk7_3_checked, root7Node179Step3Chunk7_4_checked, root7Node179Step3Chunk7_5_checked, root7Node179Step3Chunk8_0_checked, root7Node179Step3Chunk8_1_checked, root7Node179Step3Chunk8_2_checked, root7Node179Step3Chunk8_3_checked, root7Node179Step3Chunk8_4_checked, root7Node179Step3Chunk8_5_checked, Bool.true_and])
theorem root7Node179Step3_checked :
    checkReplacement table3 root7Node179Domains2 root7Node179Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root7Node179Domains2 root7Node179Domains3
    root7Node179Domains2Fast root7Node179Domains3Fast
    root7Node179Domains2_fast_eq root7Node179Domains3_fast_eq
    root7Node179Step3Narrowing_checked (by decide)
def root7Node180Domains0 : Domains 91 State := restrict root7Node179Domains3 4 (7,3)
def root7Node180Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(5,2),(5,5)]
  | 6 => some [(7,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(1,4),(6,4)]
  | 11 => some [(0,5),(1,2)]
  | 12 => some [(4,4),(8,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3),(6,0)]
  | 19 => some [(7,1),(8,1)]
  | 20 => some [(1,5),(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2),(8,2)]
  | 27 => some [(5,0),(5,3),(8,0)]
  | 28 => some [(4,5),(7,3),(8,5)]
  | 29 => some [(4,2),(7,0),(8,2)]
  | 30 => some [(7,1),(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(3,4),(5,4)]
  | 37 => some [(0,0),(6,3),(6,4)]
  | 38 => some [(1,2),(7,2)]
  | 39 => some [(7,4),(8,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(5,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(2,3),(4,3)]
  | 47 => some [(0,2),(1,5),(3,5),(7,5)]
  | 48 => some [(0,3),(1,1),(6,1)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(1,5),(6,5)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(6,4),(7,4)]
  | 57 => some [(0,5),(1,2),(1,3),(6,3)]
  | 58 => some [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 59 => some [(1,3),(3,3),(5,3),(7,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(1,1),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(1,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(0,3),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => some [(0,1),(1,4),(3,4),(6,5)]
  | 69 => some [(0,4),(0,5),(6,2),(6,3)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2),(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(4,2),(5,2),(5,5),(8,2)]
  | 75 => some [(3,0),(5,0),(5,3),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5),(8,5)]
  | 77 => some [(0,2),(1,0),(6,0),(7,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(1,4),(6,4)]
  | 81 => some [(0,5),(1,2)]
  | 82 => some [(4,4),(7,4),(8,4)]
  | 83 => some [(0,0),(1,3),(6,4)]
  | 84 => some [(1,2),(7,2),(8,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3),(6,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5),(6,5),(7,5)]
  | _ => some [(0,3),(0,4),(6,1)]
theorem root7Node180Domains0_fast_eq : root7Node180Domains0 = expandDomains root7Node180Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node180Domains0 v = expandDomains root7Node180Domains0Fast v from by decide) v
def root7Node180Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4)]
  | 1 => [(1,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3)]
  | 5 => [(5,2)]
  | 6 => [(7,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(6,4)]
  | 11 => [(1,2)]
  | 12 => [(8,4)]
  | 13 => [(5,0)]
  | 14 => [(4,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(0,3)]
  | 19 => [(8,1)]
  | 20 => [(1,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(4,2)]
  | 27 => [(5,3)]
  | 28 => [(8,5)]
  | 29 => [(7,0)]
  | 30 => [(7,1),(8,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(3,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(5,0),(5,3)]
  | 41 => [(4,5),(5,5),(8,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5)]
  | 45 => [(7,0)]
  | 46 => [(2,3)]
  | 47 => [(0,2)]
  | 48 => [(1,1)]
  | 49 => [(4,1)]
  | 50 => [(0,2)]
  | 51 => [(0,0),(0,5),(6,3)]
  | 52 => [(4,4),(7,2)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(4,0)]
  | 59 => [(7,3)]
  | 60 => [(5,2)]
  | 61 => [(1,1),(6,1),(7,1)]
  | 62 => [(4,1),(7,5)]
  | 63 => [(0,2),(6,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(5,1)]
  | 68 => [(0,1)]
  | 69 => [(6,2)]
  | 70 => [(7,3)]
  | 71 => [(5,2),(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3)]
  | 74 => [(4,2)]
  | 75 => [(5,3)]
  | 76 => [(8,5)]
  | 77 => [(1,0)]
  | 78 => [(6,2)]
  | 79 => [(8,4)]
  | 80 => [(1,4),(6,4)]
  | 81 => [(0,5),(1,2)]
  | 82 => [(4,4),(7,4),(8,4)]
  | 83 => [(0,0),(1,3),(6,4)]
  | 84 => [(1,2),(7,2),(8,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(0,3),(6,0)]
  | 88 => [(7,1),(8,1)]
  | 89 => [(1,5),(6,5),(7,5)]
  | _ => [(0,3),(0,4),(6,1)]
def root7Node180Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(5,2)]
  | 6 => some [(7,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3)]
  | 19 => some [(8,1)]
  | 20 => some [(1,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2)]
  | 27 => some [(5,3)]
  | 28 => some [(8,5)]
  | 29 => some [(7,0)]
  | 30 => some [(7,1),(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(3,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(5,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(7,0)]
  | 46 => some [(2,3)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(5,2)]
  | 61 => some [(1,1),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(5,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2),(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(1,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(1,4),(6,4)]
  | 81 => some [(0,5),(1,2)]
  | 82 => some [(4,4),(7,4),(8,4)]
  | 83 => some [(0,0),(1,3),(6,4)]
  | 84 => some [(1,2),(7,2),(8,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3),(6,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5),(6,5),(7,5)]
  | _ => some [(0,3),(0,4),(6,1)]
theorem root7Node180Domains1_fast_eq : root7Node180Domains1 = expandDomains root7Node180Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node180Domains1 v = expandDomains root7Node180Domains1Fast v from by decide) v
theorem root7Node180Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq (by decide)
theorem root7Node180Step1Narrowing_checked :
    checkNarrowing table36 root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root7Node180Domains0 root7Node180Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node180Step1Chunk0_0_checked, root7Node180Step1Chunk0_1_checked, root7Node180Step1Chunk0_2_checked, root7Node180Step1Chunk0_3_checked, root7Node180Step1Chunk0_4_checked, root7Node180Step1Chunk0_5_checked, root7Node180Step1Chunk1_0_checked, root7Node180Step1Chunk1_1_checked, root7Node180Step1Chunk1_2_checked, root7Node180Step1Chunk1_3_checked, root7Node180Step1Chunk1_4_checked, root7Node180Step1Chunk1_5_checked, root7Node180Step1Chunk2_0_checked, root7Node180Step1Chunk2_1_checked, root7Node180Step1Chunk2_2_checked, root7Node180Step1Chunk2_3_checked, root7Node180Step1Chunk2_4_checked, root7Node180Step1Chunk2_5_checked, root7Node180Step1Chunk3_0_checked, root7Node180Step1Chunk3_1_checked, root7Node180Step1Chunk3_2_checked, root7Node180Step1Chunk3_3_checked, root7Node180Step1Chunk3_4_checked, root7Node180Step1Chunk3_5_checked, root7Node180Step1Chunk4_0_checked, root7Node180Step1Chunk4_1_checked, root7Node180Step1Chunk4_2_checked, root7Node180Step1Chunk4_3_checked, root7Node180Step1Chunk4_4_checked, root7Node180Step1Chunk4_5_checked, root7Node180Step1Chunk5_0_checked, root7Node180Step1Chunk5_1_checked, root7Node180Step1Chunk5_2_checked, root7Node180Step1Chunk5_3_checked, root7Node180Step1Chunk5_4_checked, root7Node180Step1Chunk5_5_checked, root7Node180Step1Chunk6_0_checked, root7Node180Step1Chunk6_1_checked, root7Node180Step1Chunk6_2_checked, root7Node180Step1Chunk6_3_checked, root7Node180Step1Chunk6_4_checked, root7Node180Step1Chunk6_5_checked, root7Node180Step1Chunk7_0_checked, root7Node180Step1Chunk7_1_checked, root7Node180Step1Chunk7_2_checked, root7Node180Step1Chunk7_3_checked, root7Node180Step1Chunk7_4_checked, root7Node180Step1Chunk7_5_checked, root7Node180Step1Chunk8_0_checked, root7Node180Step1Chunk8_1_checked, root7Node180Step1Chunk8_2_checked, root7Node180Step1Chunk8_3_checked, root7Node180Step1Chunk8_4_checked, root7Node180Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node180Step1_checked :
    checkReplacement table36 root7Node180Domains0 root7Node180Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node180Domains0 root7Node180Domains1
    root7Node180Domains0Fast root7Node180Domains1Fast
    root7Node180Domains0_fast_eq root7Node180Domains1_fast_eq
    root7Node180Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
