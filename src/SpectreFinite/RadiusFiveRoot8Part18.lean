module

public import SpectreFinite.RadiusFiveRoot8Part17
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable55
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node42Domains0 : Domains 91 State := restrict root8Node40Domains1 39 (3,4)
def root8Node42Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(5,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(4,2)]
  | 30 => some [(4,3)]
  | 31 => some [(3,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(3,4)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(2,4)]
  | 43 => some [(1,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5)]
  | 48 => some [(3,0),(7,0)]
  | 49 => some [(2,3),(2,5)]
  | 50 => some [(0,2),(6,0)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(0,0),(6,4)]
  | 60 => some [(1,2),(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0),(8,0)]
  | 76 => some [(4,5),(7,3)]
  | 77 => some [(4,2),(7,0)]
  | 78 => some [(6,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5),(8,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(1,5),(3,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root8Node42Domains0_fast_eq : root8Node42Domains0 = expandDomains root8Node42Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node42Domains0 v = expandDomains root8Node42Domains0Fast v from by decide) v
def root8Node42Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(8,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(8,0)]
  | 14 => [(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(5,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(4,2)]
  | 30 => [(4,3)]
  | 31 => [(3,5)]
  | 32 => [(0,3)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(8,1)]
  | 37 => [(6,5)]
  | 38 => [(0,4)]
  | 39 => [(3,4)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(2,4)]
  | 43 => [(1,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(8,3)]
  | 47 => [(5,5)]
  | 48 => [(7,0)]
  | 49 => [(2,3)]
  | 50 => [(0,2)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(1,4)]
  | 57 => [(0,5)]
  | 58 => [(4,4)]
  | 59 => [(6,4)]
  | 60 => [(1,2)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(7,5)]
  | 66 => [(6,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(0,3)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(8,2)]
  | 75 => [(8,0)]
  | 76 => [(7,3)]
  | 77 => [(4,2)]
  | 78 => [(6,1)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(5,4)]
  | 83 => [(6,4)]
  | 84 => [(1,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5),(8,5)]
  | 87 => [(7,0)]
  | 88 => [(4,3)]
  | 89 => [(3,5),(7,5)]
  | _ => [(0,3)]
def root8Node42Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(5,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(4,2)]
  | 30 => some [(4,3)]
  | 31 => some [(3,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(3,4)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(2,4)]
  | 43 => some [(1,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5)]
  | 48 => some [(7,0)]
  | 49 => some [(2,3)]
  | 50 => some [(0,2)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(6,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5),(8,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(3,5),(7,5)]
  | _ => some [(0,3)]
theorem root8Node42Domains1_fast_eq : root8Node42Domains1 = expandDomains root8Node42Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node42Domains1 v = expandDomains root8Node42Domains1Fast v from by decide) v
theorem root8Node42Step1Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Narrowing_checked :
    checkNarrowing table57 root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root8Node42Domains0 root8Node42Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node42Step1Chunk0_0_checked, root8Node42Step1Chunk0_1_checked, root8Node42Step1Chunk0_2_checked, root8Node42Step1Chunk0_3_checked, root8Node42Step1Chunk0_4_checked, root8Node42Step1Chunk0_5_checked, root8Node42Step1Chunk1_0_checked, root8Node42Step1Chunk1_1_checked, root8Node42Step1Chunk1_2_checked, root8Node42Step1Chunk1_3_checked, root8Node42Step1Chunk1_4_checked, root8Node42Step1Chunk1_5_checked, root8Node42Step1Chunk2_0_checked, root8Node42Step1Chunk2_1_checked, root8Node42Step1Chunk2_2_checked, root8Node42Step1Chunk2_3_checked, root8Node42Step1Chunk2_4_checked, root8Node42Step1Chunk2_5_checked, root8Node42Step1Chunk3_0_checked, root8Node42Step1Chunk3_1_checked, root8Node42Step1Chunk3_2_checked, root8Node42Step1Chunk3_3_checked, root8Node42Step1Chunk3_4_checked, root8Node42Step1Chunk3_5_checked, root8Node42Step1Chunk4_0_checked, root8Node42Step1Chunk4_1_checked, root8Node42Step1Chunk4_2_checked, root8Node42Step1Chunk4_3_checked, root8Node42Step1Chunk4_4_checked, root8Node42Step1Chunk4_5_checked, root8Node42Step1Chunk5_0_checked, root8Node42Step1Chunk5_1_checked, root8Node42Step1Chunk5_2_checked, root8Node42Step1Chunk5_3_checked, root8Node42Step1Chunk5_4_checked, root8Node42Step1Chunk5_5_checked, root8Node42Step1Chunk6_0_checked, root8Node42Step1Chunk6_1_checked, root8Node42Step1Chunk6_2_checked, root8Node42Step1Chunk6_3_checked, root8Node42Step1Chunk6_4_checked, root8Node42Step1Chunk6_5_checked, root8Node42Step1Chunk7_0_checked, root8Node42Step1Chunk7_1_checked, root8Node42Step1Chunk7_2_checked, root8Node42Step1Chunk7_3_checked, root8Node42Step1Chunk7_4_checked, root8Node42Step1Chunk7_5_checked, root8Node42Step1Chunk8_0_checked, root8Node42Step1Chunk8_1_checked, root8Node42Step1Chunk8_2_checked, root8Node42Step1Chunk8_3_checked, root8Node42Step1Chunk8_4_checked, root8Node42Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node42Step1_checked :
    checkReplacement table57 root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq
    root8Node42Step1Narrowing_checked (by decide)
def root8Node43Domains0 : Domains 91 State := restrict root8Node42Domains1 86 (5,5)
def root8Node43Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(5,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(4,2)]
  | 30 => some [(4,3)]
  | 31 => some [(3,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(3,4)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(2,4)]
  | 43 => some [(1,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5)]
  | 48 => some [(7,0)]
  | 49 => some [(2,3)]
  | 50 => some [(0,2)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(6,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(3,5),(7,5)]
  | _ => some [(0,3)]
theorem root8Node43Domains0_fast_eq : root8Node43Domains0 = expandDomains root8Node43Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node43Domains0 v = expandDomains root8Node43Domains0Fast v from by decide) v
def root8Node43Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(8,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(8,0)]
  | 14 => [(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(5,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(4,2)]
  | 30 => [(4,3)]
  | 31 => [(3,5)]
  | 32 => [(0,3)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(8,1)]
  | 37 => [(6,5)]
  | 38 => [(0,4)]
  | 39 => [(3,4)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(2,4)]
  | 43 => [(1,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(8,3)]
  | 47 => [(5,5)]
  | 48 => [(7,0)]
  | 49 => [(2,3)]
  | 50 => [(0,2)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(1,4)]
  | 57 => [(0,5)]
  | 58 => [(4,4)]
  | 59 => [(6,4)]
  | 60 => [(1,2)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(7,5)]
  | 66 => [(6,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(0,3)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(8,2)]
  | 75 => [(8,0)]
  | 76 => [(7,3)]
  | 77 => [(4,2)]
  | 78 => [(6,1)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(5,4)]
  | 83 => [(6,4)]
  | 84 => [(1,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5)]
  | 87 => [(7,0)]
  | 88 => [(4,3)]
  | 89 => [(3,5)]
  | _ => [(0,3)]
def root8Node43Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(5,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(4,2)]
  | 30 => some [(4,3)]
  | 31 => some [(3,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(3,4)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(2,4)]
  | 43 => some [(1,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5)]
  | 48 => some [(7,0)]
  | 49 => some [(2,3)]
  | 50 => some [(0,2)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(6,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(3,5)]
  | _ => some [(0,3)]
theorem root8Node43Domains1_fast_eq : root8Node43Domains1 = expandDomains root8Node43Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node43Domains1 v = expandDomains root8Node43Domains1Fast v from by decide) v
theorem root8Node43Step1Chunk0_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_0⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk0_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_1⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk0_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_2⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk0_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_3⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk0_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_4⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk0_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_5⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk1_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_0⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk1_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_1⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk1_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_2⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk1_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_3⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk1_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_4⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk1_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_5⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk2_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_0⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk2_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_1⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk2_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_2⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk2_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_3⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk2_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_4⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk2_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_5⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk3_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_0⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk3_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_1⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk3_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_2⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk3_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_3⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk3_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_4⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk3_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_5⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk4_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_0⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk4_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_1⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk4_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_2⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk4_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_3⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk4_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_4⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk4_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_5⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk5_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_0⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk5_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_1⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk5_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_2⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk5_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_3⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk5_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_4⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk5_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_5⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk6_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_0⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk6_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_1⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk6_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_2⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk6_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_3⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk6_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_4⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk6_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_5⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk7_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_0⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk7_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_1⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk7_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_2⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk7_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_3⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk7_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_4⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk7_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_5⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk8_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_0⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk8_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_1⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk8_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_2⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk8_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_3⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk8_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_4⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Chunk8_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_5⟩
      root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq (by decide)
theorem root8Node43Step1Narrowing_checked :
    checkNarrowing table55 root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkNarrowing_flatten table55Scope [table55Rows0_0,table55Rows0_1,table55Rows0_2,table55Rows0_3,table55Rows0_4,table55Rows0_5,table55Rows1_0,table55Rows1_1,table55Rows1_2,table55Rows1_3,table55Rows1_4,table55Rows1_5,table55Rows2_0,table55Rows2_1,table55Rows2_2,table55Rows2_3,table55Rows2_4,table55Rows2_5,table55Rows3_0,table55Rows3_1,table55Rows3_2,table55Rows3_3,table55Rows3_4,table55Rows3_5,table55Rows4_0,table55Rows4_1,table55Rows4_2,table55Rows4_3,table55Rows4_4,table55Rows4_5,table55Rows5_0,table55Rows5_1,table55Rows5_2,table55Rows5_3,table55Rows5_4,table55Rows5_5,table55Rows6_0,table55Rows6_1,table55Rows6_2,table55Rows6_3,table55Rows6_4,table55Rows6_5,table55Rows7_0,table55Rows7_1,table55Rows7_2,table55Rows7_3,table55Rows7_4,table55Rows7_5,table55Rows8_0,table55Rows8_1,table55Rows8_2,table55Rows8_3,table55Rows8_4,table55Rows8_5]
    root8Node43Domains0 root8Node43Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node43Step1Chunk0_0_checked, root8Node43Step1Chunk0_1_checked, root8Node43Step1Chunk0_2_checked, root8Node43Step1Chunk0_3_checked, root8Node43Step1Chunk0_4_checked, root8Node43Step1Chunk0_5_checked, root8Node43Step1Chunk1_0_checked, root8Node43Step1Chunk1_1_checked, root8Node43Step1Chunk1_2_checked, root8Node43Step1Chunk1_3_checked, root8Node43Step1Chunk1_4_checked, root8Node43Step1Chunk1_5_checked, root8Node43Step1Chunk2_0_checked, root8Node43Step1Chunk2_1_checked, root8Node43Step1Chunk2_2_checked, root8Node43Step1Chunk2_3_checked, root8Node43Step1Chunk2_4_checked, root8Node43Step1Chunk2_5_checked, root8Node43Step1Chunk3_0_checked, root8Node43Step1Chunk3_1_checked, root8Node43Step1Chunk3_2_checked, root8Node43Step1Chunk3_3_checked, root8Node43Step1Chunk3_4_checked, root8Node43Step1Chunk3_5_checked, root8Node43Step1Chunk4_0_checked, root8Node43Step1Chunk4_1_checked, root8Node43Step1Chunk4_2_checked, root8Node43Step1Chunk4_3_checked, root8Node43Step1Chunk4_4_checked, root8Node43Step1Chunk4_5_checked, root8Node43Step1Chunk5_0_checked, root8Node43Step1Chunk5_1_checked, root8Node43Step1Chunk5_2_checked, root8Node43Step1Chunk5_3_checked, root8Node43Step1Chunk5_4_checked, root8Node43Step1Chunk5_5_checked, root8Node43Step1Chunk6_0_checked, root8Node43Step1Chunk6_1_checked, root8Node43Step1Chunk6_2_checked, root8Node43Step1Chunk6_3_checked, root8Node43Step1Chunk6_4_checked, root8Node43Step1Chunk6_5_checked, root8Node43Step1Chunk7_0_checked, root8Node43Step1Chunk7_1_checked, root8Node43Step1Chunk7_2_checked, root8Node43Step1Chunk7_3_checked, root8Node43Step1Chunk7_4_checked, root8Node43Step1Chunk7_5_checked, root8Node43Step1Chunk8_0_checked, root8Node43Step1Chunk8_1_checked, root8Node43Step1Chunk8_2_checked, root8Node43Step1Chunk8_3_checked, root8Node43Step1Chunk8_4_checked, root8Node43Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node43Step1_checked :
    checkReplacement table55 root8Node43Domains0 root8Node43Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node43Domains0 root8Node43Domains1
    root8Node43Domains0Fast root8Node43Domains1Fast
    root8Node43Domains0_fast_eq root8Node43Domains1_fast_eq
    root8Node43Step1Narrowing_checked (by decide)
theorem root8Node43Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node43Domains1 (.output 19) = true := by decide
def root8Node44Domains0 : Domains 91 State := restrict root8Node42Domains1 86 (8,5)
def root8Node44Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(5,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(4,2)]
  | 30 => some [(4,3)]
  | 31 => some [(3,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(3,4)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(2,4)]
  | 43 => some [(1,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5)]
  | 48 => some [(7,0)]
  | 49 => some [(2,3)]
  | 50 => some [(0,2)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(6,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(8,3)]
  | 86 => some [(8,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(3,5),(7,5)]
  | _ => some [(0,3)]
theorem root8Node44Domains0_fast_eq : root8Node44Domains0 = expandDomains root8Node44Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node44Domains0 v = expandDomains root8Node44Domains0Fast v from by decide) v
def root8Node44Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(8,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(8,0)]
  | 14 => [(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(5,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(4,2)]
  | 30 => [(4,3)]
  | 31 => [(3,5)]
  | 32 => [(0,3)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(8,1)]
  | 37 => [(6,5)]
  | 38 => [(0,4)]
  | 39 => [(3,4)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(2,4)]
  | 43 => [(1,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(8,3)]
  | 47 => [(5,5)]
  | 48 => [(7,0)]
  | 49 => [(2,3)]
  | 50 => [(0,2)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(1,4)]
  | 57 => [(0,5)]
  | 58 => [(4,4)]
  | 59 => [(6,4)]
  | 60 => [(1,2)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(7,5)]
  | 66 => [(6,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(0,3)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(8,2)]
  | 75 => [(8,0)]
  | 76 => [(7,3)]
  | 77 => [(4,2)]
  | 78 => [(6,1)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(5,4)]
  | 83 => [(6,4)]
  | 84 => [(1,2)]
  | 85 => [(8,3)]
  | 86 => [(8,5)]
  | 87 => [(7,0)]
  | 88 => [(4,3)]
  | 89 => [(7,5)]
  | _ => [(0,3)]
def root8Node44Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(5,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(4,2)]
  | 30 => some [(4,3)]
  | 31 => some [(3,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(3,4)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(2,4)]
  | 43 => some [(1,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5)]
  | 48 => some [(7,0)]
  | 49 => some [(2,3)]
  | 50 => some [(0,2)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(6,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(8,3)]
  | 86 => some [(8,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(7,5)]
  | _ => some [(0,3)]
theorem root8Node44Domains1_fast_eq : root8Node44Domains1 = expandDomains root8Node44Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node44Domains1 v = expandDomains root8Node44Domains1Fast v from by decide) v
theorem root8Node44Step1Chunk0_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_0⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk0_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_1⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk0_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_2⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk0_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_3⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk0_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_4⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk0_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_5⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk1_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_0⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk1_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_1⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk1_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_2⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk1_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_3⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk1_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_4⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk1_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_5⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk2_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_0⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk2_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_1⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk2_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_2⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk2_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_3⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk2_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_4⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk2_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_5⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk3_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_0⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk3_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_1⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk3_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_2⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk3_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_3⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk3_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_4⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk3_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_5⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk4_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_0⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk4_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_1⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk4_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_2⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk4_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_3⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk4_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_4⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk4_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_5⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk5_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_0⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk5_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_1⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk5_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_2⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk5_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_3⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk5_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_4⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk5_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_5⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk6_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_0⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk6_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_1⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk6_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_2⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk6_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_3⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk6_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_4⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk6_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_5⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk7_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_0⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk7_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_1⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk7_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_2⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk7_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_3⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk7_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_4⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk7_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_5⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk8_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_0⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk8_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_1⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk8_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_2⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk8_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_3⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk8_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_4⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Chunk8_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_5⟩
      root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq (by decide)
theorem root8Node44Step1Narrowing_checked :
    checkNarrowing table55 root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkNarrowing_flatten table55Scope [table55Rows0_0,table55Rows0_1,table55Rows0_2,table55Rows0_3,table55Rows0_4,table55Rows0_5,table55Rows1_0,table55Rows1_1,table55Rows1_2,table55Rows1_3,table55Rows1_4,table55Rows1_5,table55Rows2_0,table55Rows2_1,table55Rows2_2,table55Rows2_3,table55Rows2_4,table55Rows2_5,table55Rows3_0,table55Rows3_1,table55Rows3_2,table55Rows3_3,table55Rows3_4,table55Rows3_5,table55Rows4_0,table55Rows4_1,table55Rows4_2,table55Rows4_3,table55Rows4_4,table55Rows4_5,table55Rows5_0,table55Rows5_1,table55Rows5_2,table55Rows5_3,table55Rows5_4,table55Rows5_5,table55Rows6_0,table55Rows6_1,table55Rows6_2,table55Rows6_3,table55Rows6_4,table55Rows6_5,table55Rows7_0,table55Rows7_1,table55Rows7_2,table55Rows7_3,table55Rows7_4,table55Rows7_5,table55Rows8_0,table55Rows8_1,table55Rows8_2,table55Rows8_3,table55Rows8_4,table55Rows8_5]
    root8Node44Domains0 root8Node44Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node44Step1Chunk0_0_checked, root8Node44Step1Chunk0_1_checked, root8Node44Step1Chunk0_2_checked, root8Node44Step1Chunk0_3_checked, root8Node44Step1Chunk0_4_checked, root8Node44Step1Chunk0_5_checked, root8Node44Step1Chunk1_0_checked, root8Node44Step1Chunk1_1_checked, root8Node44Step1Chunk1_2_checked, root8Node44Step1Chunk1_3_checked, root8Node44Step1Chunk1_4_checked, root8Node44Step1Chunk1_5_checked, root8Node44Step1Chunk2_0_checked, root8Node44Step1Chunk2_1_checked, root8Node44Step1Chunk2_2_checked, root8Node44Step1Chunk2_3_checked, root8Node44Step1Chunk2_4_checked, root8Node44Step1Chunk2_5_checked, root8Node44Step1Chunk3_0_checked, root8Node44Step1Chunk3_1_checked, root8Node44Step1Chunk3_2_checked, root8Node44Step1Chunk3_3_checked, root8Node44Step1Chunk3_4_checked, root8Node44Step1Chunk3_5_checked, root8Node44Step1Chunk4_0_checked, root8Node44Step1Chunk4_1_checked, root8Node44Step1Chunk4_2_checked, root8Node44Step1Chunk4_3_checked, root8Node44Step1Chunk4_4_checked, root8Node44Step1Chunk4_5_checked, root8Node44Step1Chunk5_0_checked, root8Node44Step1Chunk5_1_checked, root8Node44Step1Chunk5_2_checked, root8Node44Step1Chunk5_3_checked, root8Node44Step1Chunk5_4_checked, root8Node44Step1Chunk5_5_checked, root8Node44Step1Chunk6_0_checked, root8Node44Step1Chunk6_1_checked, root8Node44Step1Chunk6_2_checked, root8Node44Step1Chunk6_3_checked, root8Node44Step1Chunk6_4_checked, root8Node44Step1Chunk6_5_checked, root8Node44Step1Chunk7_0_checked, root8Node44Step1Chunk7_1_checked, root8Node44Step1Chunk7_2_checked, root8Node44Step1Chunk7_3_checked, root8Node44Step1Chunk7_4_checked, root8Node44Step1Chunk7_5_checked, root8Node44Step1Chunk8_0_checked, root8Node44Step1Chunk8_1_checked, root8Node44Step1Chunk8_2_checked, root8Node44Step1Chunk8_3_checked, root8Node44Step1Chunk8_4_checked, root8Node44Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node44Step1_checked :
    checkReplacement table55 root8Node44Domains0 root8Node44Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node44Domains0 root8Node44Domains1
    root8Node44Domains0Fast root8Node44Domains1Fast
    root8Node44Domains0_fast_eq root8Node44Domains1_fast_eq
    root8Node44Step1Narrowing_checked (by decide)
theorem root8Node44Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node44Domains1 (.output 20) = true := by decide
def root8Node45Domains0 : Domains 91 State := restrict root8Node39Domains1 31 (7,5)
def root8Node45Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(5,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(4,2)]
  | 30 => some [(4,3)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(1,4),(3,4)]
  | 40 => some [(1,4),(7,4)]
  | 41 => some [(0,5),(6,3)]
  | 42 => some [(2,2),(2,4)]
  | 43 => some [(1,3),(3,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5)]
  | 48 => some [(3,0),(7,0)]
  | 49 => some [(2,3),(2,5)]
  | 50 => some [(0,2),(6,0)]
  | 51 => some [(0,2),(6,0)]
  | 52 => some [(1,1),(7,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(0,0),(6,4)]
  | 60 => some [(1,2),(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(4,0),(7,4)]
  | 73 => some [(1,3),(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0),(8,0)]
  | 76 => some [(4,5),(7,3)]
  | 77 => some [(4,2),(7,0)]
  | 78 => some [(6,1)]
  | 79 => some [(5,1),(8,1)]
  | 80 => some [(0,1),(6,5)]
  | 81 => some [(0,4),(6,2)]
  | 82 => some [(5,4),(8,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5),(8,5)]
  | 87 => some [(1,0),(7,0)]
  | 88 => some [(4,3),(7,1)]
  | 89 => some [(1,5),(3,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root8Node45Domains0_fast_eq : root8Node45Domains0 = expandDomains root8Node45Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node45Domains0 v = expandDomains root8Node45Domains0Fast v from by decide) v
def root8Node45Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(8,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(8,0)]
  | 14 => [(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(5,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(4,2)]
  | 30 => [(4,3)]
  | 31 => [(7,5)]
  | 32 => [(0,3)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(8,1)]
  | 37 => [(6,5)]
  | 38 => [(0,4)]
  | 39 => [(1,4),(3,4)]
  | 40 => [(7,4)]
  | 41 => [(6,3)]
  | 42 => [(2,2)]
  | 43 => [(3,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(8,3)]
  | 47 => [(5,5)]
  | 48 => [(3,0),(7,0)]
  | 49 => [(2,3),(2,5)]
  | 50 => [(0,2),(6,0)]
  | 51 => [(0,2)]
  | 52 => [(1,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(1,4)]
  | 57 => [(0,5)]
  | 58 => [(4,4)]
  | 59 => [(0,0),(6,4)]
  | 60 => [(1,2),(7,2)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(6,0)]
  | 67 => [(7,1)]
  | 68 => [(1,5),(7,5)]
  | 69 => [(0,3),(6,1)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(4,0)]
  | 73 => [(7,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0),(8,0)]
  | 76 => [(4,5),(7,3)]
  | 77 => [(4,2),(7,0)]
  | 78 => [(6,1)]
  | 79 => [(5,1)]
  | 80 => [(0,1)]
  | 81 => [(6,2)]
  | 82 => [(8,4)]
  | 83 => [(0,0),(6,4)]
  | 84 => [(1,2),(7,2)]
  | 85 => [(8,3)]
  | 86 => [(8,5)]
  | 87 => [(1,0)]
  | 88 => [(7,1)]
  | 89 => [(1,5),(3,5),(7,5)]
  | _ => [(0,3),(6,1)]
def root8Node45Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(5,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(4,2)]
  | 30 => some [(4,3)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(1,4),(3,4)]
  | 40 => some [(7,4)]
  | 41 => some [(6,3)]
  | 42 => some [(2,2)]
  | 43 => some [(3,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5)]
  | 48 => some [(3,0),(7,0)]
  | 49 => some [(2,3),(2,5)]
  | 50 => some [(0,2),(6,0)]
  | 51 => some [(0,2)]
  | 52 => some [(1,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(0,0),(6,4)]
  | 60 => some [(1,2),(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(4,0)]
  | 73 => some [(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0),(8,0)]
  | 76 => some [(4,5),(7,3)]
  | 77 => some [(4,2),(7,0)]
  | 78 => some [(6,1)]
  | 79 => some [(5,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(8,5)]
  | 87 => some [(1,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5),(3,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root8Node45Domains1_fast_eq : root8Node45Domains1 = expandDomains root8Node45Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node45Domains1 v = expandDomains root8Node45Domains1Fast v from by decide) v
theorem root8Node45Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq (by decide)
theorem root8Node45Step1Narrowing_checked :
    checkNarrowing table54 root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root8Node45Domains0 root8Node45Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node45Step1Chunk0_0_checked, root8Node45Step1Chunk0_1_checked, root8Node45Step1Chunk0_2_checked, root8Node45Step1Chunk0_3_checked, root8Node45Step1Chunk0_4_checked, root8Node45Step1Chunk0_5_checked, root8Node45Step1Chunk1_0_checked, root8Node45Step1Chunk1_1_checked, root8Node45Step1Chunk1_2_checked, root8Node45Step1Chunk1_3_checked, root8Node45Step1Chunk1_4_checked, root8Node45Step1Chunk1_5_checked, root8Node45Step1Chunk2_0_checked, root8Node45Step1Chunk2_1_checked, root8Node45Step1Chunk2_2_checked, root8Node45Step1Chunk2_3_checked, root8Node45Step1Chunk2_4_checked, root8Node45Step1Chunk2_5_checked, root8Node45Step1Chunk3_0_checked, root8Node45Step1Chunk3_1_checked, root8Node45Step1Chunk3_2_checked, root8Node45Step1Chunk3_3_checked, root8Node45Step1Chunk3_4_checked, root8Node45Step1Chunk3_5_checked, root8Node45Step1Chunk4_0_checked, root8Node45Step1Chunk4_1_checked, root8Node45Step1Chunk4_2_checked, root8Node45Step1Chunk4_3_checked, root8Node45Step1Chunk4_4_checked, root8Node45Step1Chunk4_5_checked, root8Node45Step1Chunk5_0_checked, root8Node45Step1Chunk5_1_checked, root8Node45Step1Chunk5_2_checked, root8Node45Step1Chunk5_3_checked, root8Node45Step1Chunk5_4_checked, root8Node45Step1Chunk5_5_checked, root8Node45Step1Chunk6_0_checked, root8Node45Step1Chunk6_1_checked, root8Node45Step1Chunk6_2_checked, root8Node45Step1Chunk6_3_checked, root8Node45Step1Chunk6_4_checked, root8Node45Step1Chunk6_5_checked, root8Node45Step1Chunk7_0_checked, root8Node45Step1Chunk7_1_checked, root8Node45Step1Chunk7_2_checked, root8Node45Step1Chunk7_3_checked, root8Node45Step1Chunk7_4_checked, root8Node45Step1Chunk7_5_checked, root8Node45Step1Chunk8_0_checked, root8Node45Step1Chunk8_1_checked, root8Node45Step1Chunk8_2_checked, root8Node45Step1Chunk8_3_checked, root8Node45Step1Chunk8_4_checked, root8Node45Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node45Step1_checked :
    checkReplacement table54 root8Node45Domains0 root8Node45Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node45Domains0 root8Node45Domains1
    root8Node45Domains0Fast root8Node45Domains1Fast
    root8Node45Domains0_fast_eq root8Node45Domains1_fast_eq
    root8Node45Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
