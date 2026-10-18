module

public import SpectreFinite.RadiusFiveRoot7Part72
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable12
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable44
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node184Domains0 : Domains 91 State := restrict root7Node183Domains1 29 (4,2)
def root7Node184Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(7,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(7,1),(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(7,4),(8,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(5,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(3,5),(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(1,5),(6,5)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(1,3),(6,3)]
  | 58 => some [(2,2),(2,4),(4,2)]
  | 59 => some [(1,3),(3,3),(5,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(1,1),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(1,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(7,1)]
  | 68 => some [(0,1),(1,4),(3,4),(6,5)]
  | 69 => some [(0,4),(0,5),(6,2),(6,3)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2),(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5),(8,2)]
  | 75 => some [(3,0),(5,0),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5)]
  | 77 => some [(0,2),(1,0),(6,0),(7,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(1,4),(6,4)]
  | 81 => some [(0,5),(1,2)]
  | 82 => some [(4,4),(8,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3),(6,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node184Domains0_fast_eq : root7Node184Domains0 = expandDomains root7Node184Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node184Domains0 v = expandDomains root7Node184Domains0Fast v from by decide) v
def root7Node184Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4)]
  | 1 => [(1,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(7,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(5,0)]
  | 14 => [(4,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(4,2)]
  | 30 => [(7,1),(8,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(7,4)]
  | 40 => [(5,0),(5,3)]
  | 41 => [(4,5),(5,5),(8,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(3,5),(7,5)]
  | 48 => [(0,3)]
  | 49 => [(4,1),(8,1)]
  | 50 => [(0,2),(6,5)]
  | 51 => [(0,0),(0,5),(6,3)]
  | 52 => [(4,4),(7,2)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(7,4)]
  | 57 => [(0,5),(1,3),(6,3)]
  | 58 => [(2,2),(2,4),(4,2)]
  | 59 => [(1,3),(3,3),(5,3)]
  | 60 => [(5,2),(5,5),(8,5)]
  | 61 => [(1,1),(6,1),(7,1)]
  | 62 => [(4,1),(7,5)]
  | 63 => [(0,2),(6,0)]
  | 64 => [(1,1),(7,1)]
  | 65 => [(4,1),(7,5),(8,1)]
  | 66 => [(0,2),(6,0),(6,5)]
  | 67 => [(0,4),(1,1),(7,1)]
  | 68 => [(0,1),(1,4),(3,4),(6,5)]
  | 69 => [(0,4),(0,5),(6,2),(6,3)]
  | 70 => [(7,3)]
  | 71 => [(5,2),(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(5,2),(5,5),(8,2)]
  | 75 => [(3,0),(5,0),(7,0)]
  | 76 => [(2,3),(2,5),(4,5)]
  | 77 => [(0,2),(1,0),(6,0),(7,0)]
  | 78 => [(6,2)]
  | 79 => [(8,4)]
  | 80 => [(1,4),(6,4)]
  | 81 => [(0,5),(1,2)]
  | 82 => [(4,4),(8,4)]
  | 83 => [(0,0),(6,4)]
  | 84 => [(1,2),(7,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(0,3),(6,0)]
  | 88 => [(7,1),(8,1)]
  | 89 => [(1,5),(7,5)]
  | _ => [(0,3),(6,1)]
def root7Node184Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(7,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(7,1),(8,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(5,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(3,5),(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(6,5)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(1,3),(6,3)]
  | 58 => some [(2,2),(2,4),(4,2)]
  | 59 => some [(1,3),(3,3),(5,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(1,1),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(1,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(7,1)]
  | 68 => some [(0,1),(1,4),(3,4),(6,5)]
  | 69 => some [(0,4),(0,5),(6,2),(6,3)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2),(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5),(8,2)]
  | 75 => some [(3,0),(5,0),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5)]
  | 77 => some [(0,2),(1,0),(6,0),(7,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(1,4),(6,4)]
  | 81 => some [(0,5),(1,2)]
  | 82 => some [(4,4),(8,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3),(6,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node184Domains1_fast_eq : root7Node184Domains1 = expandDomains root7Node184Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node184Domains1 v = expandDomains root7Node184Domains1Fast v from by decide) v
theorem root7Node184Step1Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq (by decide)
theorem root7Node184Step1Narrowing_checked :
    checkNarrowing table12 root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkNarrowing_flatten table12Scope [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5]
    root7Node184Domains0 root7Node184Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node184Step1Chunk0_0_checked, root7Node184Step1Chunk0_1_checked, root7Node184Step1Chunk0_2_checked, root7Node184Step1Chunk0_3_checked, root7Node184Step1Chunk0_4_checked, root7Node184Step1Chunk0_5_checked, root7Node184Step1Chunk1_0_checked, root7Node184Step1Chunk1_1_checked, root7Node184Step1Chunk1_2_checked, root7Node184Step1Chunk1_3_checked, root7Node184Step1Chunk1_4_checked, root7Node184Step1Chunk1_5_checked, root7Node184Step1Chunk2_0_checked, root7Node184Step1Chunk2_1_checked, root7Node184Step1Chunk2_2_checked, root7Node184Step1Chunk2_3_checked, root7Node184Step1Chunk2_4_checked, root7Node184Step1Chunk2_5_checked, root7Node184Step1Chunk3_0_checked, root7Node184Step1Chunk3_1_checked, root7Node184Step1Chunk3_2_checked, root7Node184Step1Chunk3_3_checked, root7Node184Step1Chunk3_4_checked, root7Node184Step1Chunk3_5_checked, root7Node184Step1Chunk4_0_checked, root7Node184Step1Chunk4_1_checked, root7Node184Step1Chunk4_2_checked, root7Node184Step1Chunk4_3_checked, root7Node184Step1Chunk4_4_checked, root7Node184Step1Chunk4_5_checked, root7Node184Step1Chunk5_0_checked, root7Node184Step1Chunk5_1_checked, root7Node184Step1Chunk5_2_checked, root7Node184Step1Chunk5_3_checked, root7Node184Step1Chunk5_4_checked, root7Node184Step1Chunk5_5_checked, root7Node184Step1Chunk6_0_checked, root7Node184Step1Chunk6_1_checked, root7Node184Step1Chunk6_2_checked, root7Node184Step1Chunk6_3_checked, root7Node184Step1Chunk6_4_checked, root7Node184Step1Chunk6_5_checked, root7Node184Step1Chunk7_0_checked, root7Node184Step1Chunk7_1_checked, root7Node184Step1Chunk7_2_checked, root7Node184Step1Chunk7_3_checked, root7Node184Step1Chunk7_4_checked, root7Node184Step1Chunk7_5_checked, root7Node184Step1Chunk8_0_checked, root7Node184Step1Chunk8_1_checked, root7Node184Step1Chunk8_2_checked, root7Node184Step1Chunk8_3_checked, root7Node184Step1Chunk8_4_checked, root7Node184Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node184Step1_checked :
    checkReplacement table12 root7Node184Domains0 root7Node184Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node184Domains0 root7Node184Domains1
    root7Node184Domains0Fast root7Node184Domains1Fast
    root7Node184Domains0_fast_eq root7Node184Domains1_fast_eq
    root7Node184Step1Narrowing_checked (by decide)
def root7Node185Domains0 : Domains 91 State := restrict root7Node184Domains1 30 (7,1)
def root7Node185Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(7,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0),(5,3)]
  | 41 => some [(4,5),(5,5),(8,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(3,5),(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(6,5)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(1,3),(6,3)]
  | 58 => some [(2,2),(2,4),(4,2)]
  | 59 => some [(1,3),(3,3),(5,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(1,1),(6,1),(7,1)]
  | 62 => some [(4,1),(7,5)]
  | 63 => some [(0,2),(6,0)]
  | 64 => some [(1,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(7,1)]
  | 68 => some [(0,1),(1,4),(3,4),(6,5)]
  | 69 => some [(0,4),(0,5),(6,2),(6,3)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2),(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5),(8,2)]
  | 75 => some [(3,0),(5,0),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5)]
  | 77 => some [(0,2),(1,0),(6,0),(7,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(1,4),(6,4)]
  | 81 => some [(0,5),(1,2)]
  | 82 => some [(4,4),(8,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3),(6,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node185Domains0_fast_eq : root7Node185Domains0 = expandDomains root7Node185Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node185Domains0 v = expandDomains root7Node185Domains0Fast v from by decide) v
def root7Node185Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4)]
  | 1 => [(1,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(7,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(5,0)]
  | 14 => [(4,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(4,2)]
  | 30 => [(7,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(7,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(4,1),(8,1)]
  | 50 => [(0,2),(6,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3),(6,3)]
  | 58 => [(2,2),(4,2)]
  | 59 => [(1,3),(3,3),(5,3)]
  | 60 => [(5,2),(5,5),(8,5)]
  | 61 => [(6,1)]
  | 62 => [(4,1)]
  | 63 => [(0,2)]
  | 64 => [(1,1)]
  | 65 => [(4,1),(8,1)]
  | 66 => [(0,2),(6,5)]
  | 67 => [(0,4),(1,1)]
  | 68 => [(0,1),(1,4),(3,4),(6,5)]
  | 69 => [(0,4),(0,5),(6,2),(6,3)]
  | 70 => [(7,3)]
  | 71 => [(5,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(5,2),(5,5)]
  | 75 => [(3,0),(5,0),(7,0)]
  | 76 => [(2,3),(2,5),(4,5)]
  | 77 => [(0,2),(1,0),(6,0),(7,0)]
  | 78 => [(6,2)]
  | 79 => [(8,4)]
  | 80 => [(1,4),(6,4)]
  | 81 => [(0,5),(1,2)]
  | 82 => [(4,4),(8,4)]
  | 83 => [(0,0),(6,4)]
  | 84 => [(1,2),(7,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(0,3),(6,0)]
  | 88 => [(7,1),(8,1)]
  | 89 => [(1,5),(7,5)]
  | _ => [(0,3),(6,1)]
def root7Node185Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(7,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3),(6,3)]
  | 58 => some [(2,2),(4,2)]
  | 59 => some [(1,3),(3,3),(5,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(4,1),(8,1)]
  | 66 => some [(0,2),(6,5)]
  | 67 => some [(0,4),(1,1)]
  | 68 => some [(0,1),(1,4),(3,4),(6,5)]
  | 69 => some [(0,4),(0,5),(6,2),(6,3)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5)]
  | 75 => some [(3,0),(5,0),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5)]
  | 77 => some [(0,2),(1,0),(6,0),(7,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(1,4),(6,4)]
  | 81 => some [(0,5),(1,2)]
  | 82 => some [(4,4),(8,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3),(6,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node185Domains1_fast_eq : root7Node185Domains1 = expandDomains root7Node185Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node185Domains1 v = expandDomains root7Node185Domains1Fast v from by decide) v
theorem root7Node185Step1Chunk0_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_0⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk0_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_1⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk0_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_2⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk0_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_3⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk0_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_4⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk0_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_5⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk1_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_0⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk1_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_1⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk1_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_2⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk1_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_3⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk1_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_4⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk1_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_5⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk2_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_0⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk2_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_1⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk2_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_2⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk2_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_3⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk2_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_4⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk2_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_5⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk3_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_0⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk3_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_1⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk3_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_2⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk3_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_3⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk3_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_4⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk3_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_5⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk4_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_0⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk4_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_1⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk4_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_2⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk4_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_3⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk4_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_4⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk4_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_5⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk5_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_0⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk5_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_1⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk5_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_2⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk5_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_3⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk5_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_4⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk5_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_5⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk6_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_0⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk6_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_1⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk6_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_2⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk6_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_3⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk6_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_4⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk6_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_5⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk7_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_0⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk7_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_1⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk7_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_2⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk7_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_3⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk7_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_4⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk7_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_5⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk8_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_0⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk8_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_1⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk8_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_2⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk8_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_3⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk8_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_4⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Chunk8_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_5⟩
      root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq (by decide)
theorem root7Node185Step1Narrowing_checked :
    checkNarrowing table44 root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkNarrowing_flatten table44Scope [table44Rows0_0,table44Rows0_1,table44Rows0_2,table44Rows0_3,table44Rows0_4,table44Rows0_5,table44Rows1_0,table44Rows1_1,table44Rows1_2,table44Rows1_3,table44Rows1_4,table44Rows1_5,table44Rows2_0,table44Rows2_1,table44Rows2_2,table44Rows2_3,table44Rows2_4,table44Rows2_5,table44Rows3_0,table44Rows3_1,table44Rows3_2,table44Rows3_3,table44Rows3_4,table44Rows3_5,table44Rows4_0,table44Rows4_1,table44Rows4_2,table44Rows4_3,table44Rows4_4,table44Rows4_5,table44Rows5_0,table44Rows5_1,table44Rows5_2,table44Rows5_3,table44Rows5_4,table44Rows5_5,table44Rows6_0,table44Rows6_1,table44Rows6_2,table44Rows6_3,table44Rows6_4,table44Rows6_5,table44Rows7_0,table44Rows7_1,table44Rows7_2,table44Rows7_3,table44Rows7_4,table44Rows7_5,table44Rows8_0,table44Rows8_1,table44Rows8_2,table44Rows8_3,table44Rows8_4,table44Rows8_5]
    root7Node185Domains0 root7Node185Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node185Step1Chunk0_0_checked, root7Node185Step1Chunk0_1_checked, root7Node185Step1Chunk0_2_checked, root7Node185Step1Chunk0_3_checked, root7Node185Step1Chunk0_4_checked, root7Node185Step1Chunk0_5_checked, root7Node185Step1Chunk1_0_checked, root7Node185Step1Chunk1_1_checked, root7Node185Step1Chunk1_2_checked, root7Node185Step1Chunk1_3_checked, root7Node185Step1Chunk1_4_checked, root7Node185Step1Chunk1_5_checked, root7Node185Step1Chunk2_0_checked, root7Node185Step1Chunk2_1_checked, root7Node185Step1Chunk2_2_checked, root7Node185Step1Chunk2_3_checked, root7Node185Step1Chunk2_4_checked, root7Node185Step1Chunk2_5_checked, root7Node185Step1Chunk3_0_checked, root7Node185Step1Chunk3_1_checked, root7Node185Step1Chunk3_2_checked, root7Node185Step1Chunk3_3_checked, root7Node185Step1Chunk3_4_checked, root7Node185Step1Chunk3_5_checked, root7Node185Step1Chunk4_0_checked, root7Node185Step1Chunk4_1_checked, root7Node185Step1Chunk4_2_checked, root7Node185Step1Chunk4_3_checked, root7Node185Step1Chunk4_4_checked, root7Node185Step1Chunk4_5_checked, root7Node185Step1Chunk5_0_checked, root7Node185Step1Chunk5_1_checked, root7Node185Step1Chunk5_2_checked, root7Node185Step1Chunk5_3_checked, root7Node185Step1Chunk5_4_checked, root7Node185Step1Chunk5_5_checked, root7Node185Step1Chunk6_0_checked, root7Node185Step1Chunk6_1_checked, root7Node185Step1Chunk6_2_checked, root7Node185Step1Chunk6_3_checked, root7Node185Step1Chunk6_4_checked, root7Node185Step1Chunk6_5_checked, root7Node185Step1Chunk7_0_checked, root7Node185Step1Chunk7_1_checked, root7Node185Step1Chunk7_2_checked, root7Node185Step1Chunk7_3_checked, root7Node185Step1Chunk7_4_checked, root7Node185Step1Chunk7_5_checked, root7Node185Step1Chunk8_0_checked, root7Node185Step1Chunk8_1_checked, root7Node185Step1Chunk8_2_checked, root7Node185Step1Chunk8_3_checked, root7Node185Step1Chunk8_4_checked, root7Node185Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node185Step1_checked :
    checkReplacement table44 root7Node185Domains0 root7Node185Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node185Domains0 root7Node185Domains1
    root7Node185Domains0Fast root7Node185Domains1Fast
    root7Node185Domains0_fast_eq root7Node185Domains1_fast_eq
    root7Node185Step1Narrowing_checked (by decide)
def root7Node185Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4)]
  | 1 => [(1,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(7,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(5,0)]
  | 14 => [(4,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(4,2)]
  | 30 => [(7,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(7,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(4,1),(8,1)]
  | 50 => [(0,2),(6,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3),(6,3)]
  | 58 => [(2,2),(4,2)]
  | 59 => [(3,3),(5,3)]
  | 60 => [(5,2),(5,5),(8,5)]
  | 61 => [(6,1)]
  | 62 => [(4,1)]
  | 63 => [(0,2)]
  | 64 => [(1,1)]
  | 65 => [(4,1),(8,1)]
  | 66 => [(0,2),(6,5)]
  | 67 => [(0,4),(1,1)]
  | 68 => [(0,1),(1,4),(3,4)]
  | 69 => [(0,5),(6,2),(6,3)]
  | 70 => [(7,3)]
  | 71 => [(5,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(5,2),(5,5)]
  | 75 => [(3,0),(5,0),(7,0)]
  | 76 => [(2,3),(2,5),(4,5)]
  | 77 => [(0,2),(1,0),(6,0)]
  | 78 => [(6,2)]
  | 79 => [(8,4)]
  | 80 => [(1,4),(6,4)]
  | 81 => [(0,5),(1,2)]
  | 82 => [(4,4),(8,4)]
  | 83 => [(0,0),(6,4)]
  | 84 => [(1,2),(7,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(0,3),(6,0)]
  | 88 => [(7,1),(8,1)]
  | 89 => [(1,5),(7,5)]
  | _ => [(0,3),(6,1)]
def root7Node185Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(7,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(4,1),(8,1)]
  | 50 => some [(0,2),(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3),(6,3)]
  | 58 => some [(2,2),(4,2)]
  | 59 => some [(3,3),(5,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(4,1),(8,1)]
  | 66 => some [(0,2),(6,5)]
  | 67 => some [(0,4),(1,1)]
  | 68 => some [(0,1),(1,4),(3,4)]
  | 69 => some [(0,5),(6,2),(6,3)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5)]
  | 75 => some [(3,0),(5,0),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5)]
  | 77 => some [(0,2),(1,0),(6,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(1,4),(6,4)]
  | 81 => some [(0,5),(1,2)]
  | 82 => some [(4,4),(8,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3),(6,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node185Domains2_fast_eq : root7Node185Domains2 = expandDomains root7Node185Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node185Domains2 v = expandDomains root7Node185Domains2Fast v from by decide) v
theorem root7Node185Step2Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq (by decide)
theorem root7Node185Step2Narrowing_checked :
    checkNarrowing table36 root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root7Node185Domains1 root7Node185Domains2 (by
      simp only [List.all_cons, List.all_nil, root7Node185Step2Chunk0_0_checked, root7Node185Step2Chunk0_1_checked, root7Node185Step2Chunk0_2_checked, root7Node185Step2Chunk0_3_checked, root7Node185Step2Chunk0_4_checked, root7Node185Step2Chunk0_5_checked, root7Node185Step2Chunk1_0_checked, root7Node185Step2Chunk1_1_checked, root7Node185Step2Chunk1_2_checked, root7Node185Step2Chunk1_3_checked, root7Node185Step2Chunk1_4_checked, root7Node185Step2Chunk1_5_checked, root7Node185Step2Chunk2_0_checked, root7Node185Step2Chunk2_1_checked, root7Node185Step2Chunk2_2_checked, root7Node185Step2Chunk2_3_checked, root7Node185Step2Chunk2_4_checked, root7Node185Step2Chunk2_5_checked, root7Node185Step2Chunk3_0_checked, root7Node185Step2Chunk3_1_checked, root7Node185Step2Chunk3_2_checked, root7Node185Step2Chunk3_3_checked, root7Node185Step2Chunk3_4_checked, root7Node185Step2Chunk3_5_checked, root7Node185Step2Chunk4_0_checked, root7Node185Step2Chunk4_1_checked, root7Node185Step2Chunk4_2_checked, root7Node185Step2Chunk4_3_checked, root7Node185Step2Chunk4_4_checked, root7Node185Step2Chunk4_5_checked, root7Node185Step2Chunk5_0_checked, root7Node185Step2Chunk5_1_checked, root7Node185Step2Chunk5_2_checked, root7Node185Step2Chunk5_3_checked, root7Node185Step2Chunk5_4_checked, root7Node185Step2Chunk5_5_checked, root7Node185Step2Chunk6_0_checked, root7Node185Step2Chunk6_1_checked, root7Node185Step2Chunk6_2_checked, root7Node185Step2Chunk6_3_checked, root7Node185Step2Chunk6_4_checked, root7Node185Step2Chunk6_5_checked, root7Node185Step2Chunk7_0_checked, root7Node185Step2Chunk7_1_checked, root7Node185Step2Chunk7_2_checked, root7Node185Step2Chunk7_3_checked, root7Node185Step2Chunk7_4_checked, root7Node185Step2Chunk7_5_checked, root7Node185Step2Chunk8_0_checked, root7Node185Step2Chunk8_1_checked, root7Node185Step2Chunk8_2_checked, root7Node185Step2Chunk8_3_checked, root7Node185Step2Chunk8_4_checked, root7Node185Step2Chunk8_5_checked, Bool.true_and])
theorem root7Node185Step2_checked :
    checkReplacement table36 root7Node185Domains1 root7Node185Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root7Node185Domains1 root7Node185Domains2
    root7Node185Domains1Fast root7Node185Domains2Fast
    root7Node185Domains1_fast_eq root7Node185Domains2_fast_eq
    root7Node185Step2Narrowing_checked (by decide)
def root7Node186Domains0 : Domains 91 State := restrict root7Node185Domains2 49 (4,1)
def root7Node186Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(7,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2),(6,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3),(6,3)]
  | 58 => some [(2,2),(4,2)]
  | 59 => some [(3,3),(5,3)]
  | 60 => some [(5,2),(5,5),(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(4,1),(8,1)]
  | 66 => some [(0,2),(6,5)]
  | 67 => some [(0,4),(1,1)]
  | 68 => some [(0,1),(1,4),(3,4)]
  | 69 => some [(0,5),(6,2),(6,3)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5)]
  | 75 => some [(3,0),(5,0),(7,0)]
  | 76 => some [(2,3),(2,5),(4,5)]
  | 77 => some [(0,2),(1,0),(6,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(1,4),(6,4)]
  | 81 => some [(0,5),(1,2)]
  | 82 => some [(4,4),(8,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3),(6,0)]
  | 88 => some [(7,1),(8,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node186Domains0_fast_eq : root7Node186Domains0 = expandDomains root7Node186Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node186Domains0 v = expandDomains root7Node186Domains0Fast v from by decide) v
def root7Node186Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4)]
  | 1 => [(1,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(8,3)]
  | 5 => [(5,5)]
  | 6 => [(7,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(1,4)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(5,0)]
  | 14 => [(4,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(8,4)]
  | 22 => [(0,0)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(4,2)]
  | 30 => [(7,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(7,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(4,1)]
  | 50 => [(0,2)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(6,3)]
  | 58 => [(2,2)]
  | 59 => [(3,3)]
  | 60 => [(5,2)]
  | 61 => [(6,1)]
  | 62 => [(4,1)]
  | 63 => [(0,2)]
  | 64 => [(1,1)]
  | 65 => [(4,1)]
  | 66 => [(0,2)]
  | 67 => [(1,1)]
  | 68 => [(0,1)]
  | 69 => [(6,2)]
  | 70 => [(7,3)]
  | 71 => [(5,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3)]
  | 74 => [(5,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(1,0)]
  | 78 => [(6,2)]
  | 79 => [(8,4)]
  | 80 => [(6,4)]
  | 81 => [(1,2)]
  | 82 => [(8,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(0,3)]
  | 88 => [(8,1)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root7Node186Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4)]
  | 1 => some [(1,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(8,3)]
  | 5 => some [(5,5)]
  | 6 => some [(7,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(1,4)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(5,0)]
  | 14 => some [(4,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(8,4)]
  | 22 => some [(0,0)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(4,2)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(7,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(6,3)]
  | 58 => some [(2,2)]
  | 59 => some [(3,3)]
  | 60 => some [(5,2)]
  | 61 => some [(6,1)]
  | 62 => some [(4,1)]
  | 63 => some [(0,2)]
  | 64 => some [(1,1)]
  | 65 => some [(4,1)]
  | 66 => some [(0,2)]
  | 67 => some [(1,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(7,3)]
  | 71 => some [(5,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(5,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(1,0)]
  | 78 => some [(6,2)]
  | 79 => some [(8,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3)]
  | 88 => some [(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root7Node186Domains1_fast_eq : root7Node186Domains1 = expandDomains root7Node186Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node186Domains1 v = expandDomains root7Node186Domains1Fast v from by decide) v
theorem root7Node186Step1Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq (by decide)
theorem root7Node186Step1Narrowing_checked :
    checkNarrowing table57 root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root7Node186Domains0 root7Node186Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node186Step1Chunk0_0_checked, root7Node186Step1Chunk0_1_checked, root7Node186Step1Chunk0_2_checked, root7Node186Step1Chunk0_3_checked, root7Node186Step1Chunk0_4_checked, root7Node186Step1Chunk0_5_checked, root7Node186Step1Chunk1_0_checked, root7Node186Step1Chunk1_1_checked, root7Node186Step1Chunk1_2_checked, root7Node186Step1Chunk1_3_checked, root7Node186Step1Chunk1_4_checked, root7Node186Step1Chunk1_5_checked, root7Node186Step1Chunk2_0_checked, root7Node186Step1Chunk2_1_checked, root7Node186Step1Chunk2_2_checked, root7Node186Step1Chunk2_3_checked, root7Node186Step1Chunk2_4_checked, root7Node186Step1Chunk2_5_checked, root7Node186Step1Chunk3_0_checked, root7Node186Step1Chunk3_1_checked, root7Node186Step1Chunk3_2_checked, root7Node186Step1Chunk3_3_checked, root7Node186Step1Chunk3_4_checked, root7Node186Step1Chunk3_5_checked, root7Node186Step1Chunk4_0_checked, root7Node186Step1Chunk4_1_checked, root7Node186Step1Chunk4_2_checked, root7Node186Step1Chunk4_3_checked, root7Node186Step1Chunk4_4_checked, root7Node186Step1Chunk4_5_checked, root7Node186Step1Chunk5_0_checked, root7Node186Step1Chunk5_1_checked, root7Node186Step1Chunk5_2_checked, root7Node186Step1Chunk5_3_checked, root7Node186Step1Chunk5_4_checked, root7Node186Step1Chunk5_5_checked, root7Node186Step1Chunk6_0_checked, root7Node186Step1Chunk6_1_checked, root7Node186Step1Chunk6_2_checked, root7Node186Step1Chunk6_3_checked, root7Node186Step1Chunk6_4_checked, root7Node186Step1Chunk6_5_checked, root7Node186Step1Chunk7_0_checked, root7Node186Step1Chunk7_1_checked, root7Node186Step1Chunk7_2_checked, root7Node186Step1Chunk7_3_checked, root7Node186Step1Chunk7_4_checked, root7Node186Step1Chunk7_5_checked, root7Node186Step1Chunk8_0_checked, root7Node186Step1Chunk8_1_checked, root7Node186Step1Chunk8_2_checked, root7Node186Step1Chunk8_3_checked, root7Node186Step1Chunk8_4_checked, root7Node186Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node186Step1_checked :
    checkReplacement table57 root7Node186Domains0 root7Node186Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node186Domains0 root7Node186Domains1
    root7Node186Domains0Fast root7Node186Domains1Fast
    root7Node186Domains0_fast_eq root7Node186Domains1_fast_eq
    root7Node186Step1Narrowing_checked (by decide)
theorem root7Node186Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node186Domains1 (.output 91) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
