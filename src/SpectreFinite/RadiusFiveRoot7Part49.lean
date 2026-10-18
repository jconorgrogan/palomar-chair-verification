module

public import SpectreFinite.RadiusFiveRoot7Part48
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable56
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node123Domains0 : Domains 91 State := restrict root7Node121Domains1 50 (7,5)
def root7Node123Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(4,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(2,4)]
  | 25 => some [(1,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
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
  | 84 => some [(0,5),(1,3),(6,3)]
  | 85 => some [(1,1),(7,1)]
  | 86 => some [(4,1),(7,5)]
  | 87 => some [(0,2),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(4,1),(7,5),(8,1)]
  | _ => some [(0,2),(6,0),(6,5)]
theorem root7Node123Domains0_fast_eq : root7Node123Domains0 = expandDomains root7Node123Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node123Domains0 v = expandDomains root7Node123Domains0Fast v from by decide) v
def root7Node123Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(8,0)]
  | 2 => [(7,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(8,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(6,4)]
  | 9 => [(1,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(3,5)]
  | 16 => [(0,3)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(8,1)]
  | 21 => [(4,4)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(2,4)]
  | 25 => [(1,3)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(4,4)]
  | 40 => [(8,0)]
  | 41 => [(7,3)]
  | 42 => [(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
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
  | 84 => [(0,5),(1,3),(6,3)]
  | 85 => [(1,1),(7,1)]
  | 86 => [(4,1),(7,5)]
  | 87 => [(0,2),(6,0)]
  | 88 => [(1,1),(7,1)]
  | 89 => [(4,1),(7,5),(8,1)]
  | _ => [(0,2),(6,0),(6,5)]
def root7Node123Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(4,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(2,4)]
  | 25 => some [(1,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
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
  | 84 => some [(0,5),(1,3),(6,3)]
  | 85 => some [(1,1),(7,1)]
  | 86 => some [(4,1),(7,5)]
  | 87 => some [(0,2),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(4,1),(7,5),(8,1)]
  | _ => some [(0,2),(6,0),(6,5)]
theorem root7Node123Domains1_fast_eq : root7Node123Domains1 = expandDomains root7Node123Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node123Domains1 v = expandDomains root7Node123Domains1Fast v from by decide) v
theorem root7Node123Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq (by decide)
theorem root7Node123Step1Narrowing_checked :
    checkNarrowing table36 root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root7Node123Domains0 root7Node123Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node123Step1Chunk0_0_checked, root7Node123Step1Chunk0_1_checked, root7Node123Step1Chunk0_2_checked, root7Node123Step1Chunk0_3_checked, root7Node123Step1Chunk0_4_checked, root7Node123Step1Chunk0_5_checked, root7Node123Step1Chunk1_0_checked, root7Node123Step1Chunk1_1_checked, root7Node123Step1Chunk1_2_checked, root7Node123Step1Chunk1_3_checked, root7Node123Step1Chunk1_4_checked, root7Node123Step1Chunk1_5_checked, root7Node123Step1Chunk2_0_checked, root7Node123Step1Chunk2_1_checked, root7Node123Step1Chunk2_2_checked, root7Node123Step1Chunk2_3_checked, root7Node123Step1Chunk2_4_checked, root7Node123Step1Chunk2_5_checked, root7Node123Step1Chunk3_0_checked, root7Node123Step1Chunk3_1_checked, root7Node123Step1Chunk3_2_checked, root7Node123Step1Chunk3_3_checked, root7Node123Step1Chunk3_4_checked, root7Node123Step1Chunk3_5_checked, root7Node123Step1Chunk4_0_checked, root7Node123Step1Chunk4_1_checked, root7Node123Step1Chunk4_2_checked, root7Node123Step1Chunk4_3_checked, root7Node123Step1Chunk4_4_checked, root7Node123Step1Chunk4_5_checked, root7Node123Step1Chunk5_0_checked, root7Node123Step1Chunk5_1_checked, root7Node123Step1Chunk5_2_checked, root7Node123Step1Chunk5_3_checked, root7Node123Step1Chunk5_4_checked, root7Node123Step1Chunk5_5_checked, root7Node123Step1Chunk6_0_checked, root7Node123Step1Chunk6_1_checked, root7Node123Step1Chunk6_2_checked, root7Node123Step1Chunk6_3_checked, root7Node123Step1Chunk6_4_checked, root7Node123Step1Chunk6_5_checked, root7Node123Step1Chunk7_0_checked, root7Node123Step1Chunk7_1_checked, root7Node123Step1Chunk7_2_checked, root7Node123Step1Chunk7_3_checked, root7Node123Step1Chunk7_4_checked, root7Node123Step1Chunk7_5_checked, root7Node123Step1Chunk8_0_checked, root7Node123Step1Chunk8_1_checked, root7Node123Step1Chunk8_2_checked, root7Node123Step1Chunk8_3_checked, root7Node123Step1Chunk8_4_checked, root7Node123Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node123Step1_checked :
    checkReplacement table36 root7Node123Domains0 root7Node123Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node123Domains0 root7Node123Domains1
    root7Node123Domains0Fast root7Node123Domains1Fast
    root7Node123Domains0_fast_eq root7Node123Domains1_fast_eq
    root7Node123Step1Narrowing_checked (by decide)
def root7Node124Domains0 : Domains 91 State := restrict root7Node123Domains1 71 (5,5)
def root7Node124Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(4,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(2,4)]
  | 25 => some [(1,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
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
  | 71 => some [(5,5)]
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
  | 84 => some [(0,5),(1,3),(6,3)]
  | 85 => some [(1,1),(7,1)]
  | 86 => some [(4,1),(7,5)]
  | 87 => some [(0,2),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(4,1),(7,5),(8,1)]
  | _ => some [(0,2),(6,0),(6,5)]
theorem root7Node124Domains0_fast_eq : root7Node124Domains0 = expandDomains root7Node124Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node124Domains0 v = expandDomains root7Node124Domains0Fast v from by decide) v
def root7Node124Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(8,0)]
  | 2 => [(7,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(8,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(6,4)]
  | 9 => [(1,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(3,5)]
  | 16 => [(0,3)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(8,1)]
  | 21 => [(4,4)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(2,4)]
  | 25 => [(1,3)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(4,4)]
  | 40 => [(8,0)]
  | 41 => [(7,3)]
  | 42 => [(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
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
  | 71 => [(5,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5)]
  | 75 => [(7,0)]
  | 76 => [(4,3)]
  | 77 => [(3,5)]
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
def root7Node124Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(4,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(2,4)]
  | 25 => some [(1,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
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
  | 71 => some [(5,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(7,0)]
  | 76 => some [(4,3)]
  | 77 => some [(3,5)]
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
theorem root7Node124Domains1_fast_eq : root7Node124Domains1 = expandDomains root7Node124Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node124Domains1 v = expandDomains root7Node124Domains1Fast v from by decide) v
theorem root7Node124Step1Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq (by decide)
theorem root7Node124Step1Narrowing_checked :
    checkNarrowing table65 root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root7Node124Domains0 root7Node124Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node124Step1Chunk0_0_checked, root7Node124Step1Chunk0_1_checked, root7Node124Step1Chunk0_2_checked, root7Node124Step1Chunk0_3_checked, root7Node124Step1Chunk0_4_checked, root7Node124Step1Chunk0_5_checked, root7Node124Step1Chunk1_0_checked, root7Node124Step1Chunk1_1_checked, root7Node124Step1Chunk1_2_checked, root7Node124Step1Chunk1_3_checked, root7Node124Step1Chunk1_4_checked, root7Node124Step1Chunk1_5_checked, root7Node124Step1Chunk2_0_checked, root7Node124Step1Chunk2_1_checked, root7Node124Step1Chunk2_2_checked, root7Node124Step1Chunk2_3_checked, root7Node124Step1Chunk2_4_checked, root7Node124Step1Chunk2_5_checked, root7Node124Step1Chunk3_0_checked, root7Node124Step1Chunk3_1_checked, root7Node124Step1Chunk3_2_checked, root7Node124Step1Chunk3_3_checked, root7Node124Step1Chunk3_4_checked, root7Node124Step1Chunk3_5_checked, root7Node124Step1Chunk4_0_checked, root7Node124Step1Chunk4_1_checked, root7Node124Step1Chunk4_2_checked, root7Node124Step1Chunk4_3_checked, root7Node124Step1Chunk4_4_checked, root7Node124Step1Chunk4_5_checked, root7Node124Step1Chunk5_0_checked, root7Node124Step1Chunk5_1_checked, root7Node124Step1Chunk5_2_checked, root7Node124Step1Chunk5_3_checked, root7Node124Step1Chunk5_4_checked, root7Node124Step1Chunk5_5_checked, root7Node124Step1Chunk6_0_checked, root7Node124Step1Chunk6_1_checked, root7Node124Step1Chunk6_2_checked, root7Node124Step1Chunk6_3_checked, root7Node124Step1Chunk6_4_checked, root7Node124Step1Chunk6_5_checked, root7Node124Step1Chunk7_0_checked, root7Node124Step1Chunk7_1_checked, root7Node124Step1Chunk7_2_checked, root7Node124Step1Chunk7_3_checked, root7Node124Step1Chunk7_4_checked, root7Node124Step1Chunk7_5_checked, root7Node124Step1Chunk8_0_checked, root7Node124Step1Chunk8_1_checked, root7Node124Step1Chunk8_2_checked, root7Node124Step1Chunk8_3_checked, root7Node124Step1Chunk8_4_checked, root7Node124Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node124Step1_checked :
    checkReplacement table65 root7Node124Domains0 root7Node124Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node124Domains0 root7Node124Domains1
    root7Node124Domains0Fast root7Node124Domains1Fast
    root7Node124Domains0_fast_eq root7Node124Domains1_fast_eq
    root7Node124Step1Narrowing_checked (by decide)
theorem root7Node124Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node124Domains1 (.output 61) = true := by decide
def root7Node125Domains0 : Domains 91 State := restrict root7Node123Domains1 71 (8,5)
def root7Node125Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(4,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(2,4)]
  | 25 => some [(1,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
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
  | 71 => some [(8,5)]
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
  | 84 => some [(0,5),(1,3),(6,3)]
  | 85 => some [(1,1),(7,1)]
  | 86 => some [(4,1),(7,5)]
  | 87 => some [(0,2),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(4,1),(7,5),(8,1)]
  | _ => some [(0,2),(6,0),(6,5)]
theorem root7Node125Domains0_fast_eq : root7Node125Domains0 = expandDomains root7Node125Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node125Domains0 v = expandDomains root7Node125Domains0Fast v from by decide) v
def root7Node125Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(8,0)]
  | 2 => [(7,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(8,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(6,4)]
  | 9 => [(1,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(3,5)]
  | 16 => [(0,3)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(8,1)]
  | 21 => [(4,4)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(2,4)]
  | 25 => [(1,3)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(4,4)]
  | 40 => [(8,0)]
  | 41 => [(7,3)]
  | 42 => [(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
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
  | 71 => [(8,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(8,5)]
  | 75 => [(7,0)]
  | 76 => [(4,3)]
  | 77 => [(7,5)]
  | 78 => [(6,3)]
  | 79 => [(7,2)]
  | 80 => [(7,4)]
  | 81 => [(6,3)]
  | 82 => [(7,2)]
  | 83 => [(7,4)]
  | 84 => [(1,3),(6,3)]
  | 85 => [(1,1)]
  | 86 => [(4,1)]
  | 87 => [(0,2)]
  | 88 => [(1,1)]
  | 89 => [(4,1),(8,1)]
  | _ => [(0,2),(6,5)]
def root7Node125Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(4,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(2,4)]
  | 25 => some [(1,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
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
  | 71 => some [(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(8,5)]
  | 75 => some [(7,0)]
  | 76 => some [(4,3)]
  | 77 => some [(7,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(6,3)]
  | 82 => some [(7,2)]
  | 83 => some [(7,4)]
  | 84 => some [(1,3),(6,3)]
  | 85 => some [(1,1)]
  | 86 => some [(4,1)]
  | 87 => some [(0,2)]
  | 88 => some [(1,1)]
  | 89 => some [(4,1),(8,1)]
  | _ => some [(0,2),(6,5)]
theorem root7Node125Domains1_fast_eq : root7Node125Domains1 = expandDomains root7Node125Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node125Domains1 v = expandDomains root7Node125Domains1Fast v from by decide) v
theorem root7Node125Step1Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq (by decide)
theorem root7Node125Step1Narrowing_checked :
    checkNarrowing table65 root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root7Node125Domains0 root7Node125Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node125Step1Chunk0_0_checked, root7Node125Step1Chunk0_1_checked, root7Node125Step1Chunk0_2_checked, root7Node125Step1Chunk0_3_checked, root7Node125Step1Chunk0_4_checked, root7Node125Step1Chunk0_5_checked, root7Node125Step1Chunk1_0_checked, root7Node125Step1Chunk1_1_checked, root7Node125Step1Chunk1_2_checked, root7Node125Step1Chunk1_3_checked, root7Node125Step1Chunk1_4_checked, root7Node125Step1Chunk1_5_checked, root7Node125Step1Chunk2_0_checked, root7Node125Step1Chunk2_1_checked, root7Node125Step1Chunk2_2_checked, root7Node125Step1Chunk2_3_checked, root7Node125Step1Chunk2_4_checked, root7Node125Step1Chunk2_5_checked, root7Node125Step1Chunk3_0_checked, root7Node125Step1Chunk3_1_checked, root7Node125Step1Chunk3_2_checked, root7Node125Step1Chunk3_3_checked, root7Node125Step1Chunk3_4_checked, root7Node125Step1Chunk3_5_checked, root7Node125Step1Chunk4_0_checked, root7Node125Step1Chunk4_1_checked, root7Node125Step1Chunk4_2_checked, root7Node125Step1Chunk4_3_checked, root7Node125Step1Chunk4_4_checked, root7Node125Step1Chunk4_5_checked, root7Node125Step1Chunk5_0_checked, root7Node125Step1Chunk5_1_checked, root7Node125Step1Chunk5_2_checked, root7Node125Step1Chunk5_3_checked, root7Node125Step1Chunk5_4_checked, root7Node125Step1Chunk5_5_checked, root7Node125Step1Chunk6_0_checked, root7Node125Step1Chunk6_1_checked, root7Node125Step1Chunk6_2_checked, root7Node125Step1Chunk6_3_checked, root7Node125Step1Chunk6_4_checked, root7Node125Step1Chunk6_5_checked, root7Node125Step1Chunk7_0_checked, root7Node125Step1Chunk7_1_checked, root7Node125Step1Chunk7_2_checked, root7Node125Step1Chunk7_3_checked, root7Node125Step1Chunk7_4_checked, root7Node125Step1Chunk7_5_checked, root7Node125Step1Chunk8_0_checked, root7Node125Step1Chunk8_1_checked, root7Node125Step1Chunk8_2_checked, root7Node125Step1Chunk8_3_checked, root7Node125Step1Chunk8_4_checked, root7Node125Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node125Step1_checked :
    checkReplacement table65 root7Node125Domains0 root7Node125Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node125Domains0 root7Node125Domains1
    root7Node125Domains0Fast root7Node125Domains1Fast
    root7Node125Domains0_fast_eq root7Node125Domains1_fast_eq
    root7Node125Step1Narrowing_checked (by decide)
def root7Node126Domains0 : Domains 91 State := restrict root7Node125Domains1 84 (1,3)
def root7Node126Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(4,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(2,4)]
  | 25 => some [(1,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
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
  | 71 => some [(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(8,5)]
  | 75 => some [(7,0)]
  | 76 => some [(4,3)]
  | 77 => some [(7,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(6,3)]
  | 82 => some [(7,2)]
  | 83 => some [(7,4)]
  | 84 => some [(1,3)]
  | 85 => some [(1,1)]
  | 86 => some [(4,1)]
  | 87 => some [(0,2)]
  | 88 => some [(1,1)]
  | 89 => some [(4,1),(8,1)]
  | _ => some [(0,2),(6,5)]
theorem root7Node126Domains0_fast_eq : root7Node126Domains0 = expandDomains root7Node126Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node126Domains0 v = expandDomains root7Node126Domains0Fast v from by decide) v
def root7Node126Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(8,0)]
  | 2 => [(7,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(8,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(6,4)]
  | 9 => [(1,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(3,5)]
  | 16 => [(0,3)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(8,1)]
  | 21 => [(4,4)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(2,4)]
  | 25 => [(1,3)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(4,4)]
  | 40 => [(8,0)]
  | 41 => [(7,3)]
  | 42 => [(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
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
  | 71 => [(8,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(8,5)]
  | 75 => [(7,0)]
  | 76 => [(4,3)]
  | 77 => [(7,5)]
  | 78 => [(6,3)]
  | 79 => [(7,2)]
  | 80 => [(7,4)]
  | 81 => [(6,3)]
  | 82 => [(7,2)]
  | 83 => [(7,4)]
  | 84 => [(1,3)]
  | 85 => [(1,1)]
  | 86 => [(4,1)]
  | 87 => [(0,2)]
  | 88 => [(1,1)]
  | 89 => [(8,1)]
  | _ => [(6,5)]
def root7Node126Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(4,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(2,4)]
  | 25 => some [(1,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
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
  | 71 => some [(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(8,5)]
  | 75 => some [(7,0)]
  | 76 => some [(4,3)]
  | 77 => some [(7,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(6,3)]
  | 82 => some [(7,2)]
  | 83 => some [(7,4)]
  | 84 => some [(1,3)]
  | 85 => some [(1,1)]
  | 86 => some [(4,1)]
  | 87 => some [(0,2)]
  | 88 => some [(1,1)]
  | 89 => some [(8,1)]
  | _ => some [(6,5)]
theorem root7Node126Domains1_fast_eq : root7Node126Domains1 = expandDomains root7Node126Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node126Domains1 v = expandDomains root7Node126Domains1Fast v from by decide) v
theorem root7Node126Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq (by decide)
theorem root7Node126Step1Narrowing_checked :
    checkNarrowing table56 root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root7Node126Domains0 root7Node126Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node126Step1Chunk0_0_checked, root7Node126Step1Chunk0_1_checked, root7Node126Step1Chunk0_2_checked, root7Node126Step1Chunk0_3_checked, root7Node126Step1Chunk0_4_checked, root7Node126Step1Chunk0_5_checked, root7Node126Step1Chunk1_0_checked, root7Node126Step1Chunk1_1_checked, root7Node126Step1Chunk1_2_checked, root7Node126Step1Chunk1_3_checked, root7Node126Step1Chunk1_4_checked, root7Node126Step1Chunk1_5_checked, root7Node126Step1Chunk2_0_checked, root7Node126Step1Chunk2_1_checked, root7Node126Step1Chunk2_2_checked, root7Node126Step1Chunk2_3_checked, root7Node126Step1Chunk2_4_checked, root7Node126Step1Chunk2_5_checked, root7Node126Step1Chunk3_0_checked, root7Node126Step1Chunk3_1_checked, root7Node126Step1Chunk3_2_checked, root7Node126Step1Chunk3_3_checked, root7Node126Step1Chunk3_4_checked, root7Node126Step1Chunk3_5_checked, root7Node126Step1Chunk4_0_checked, root7Node126Step1Chunk4_1_checked, root7Node126Step1Chunk4_2_checked, root7Node126Step1Chunk4_3_checked, root7Node126Step1Chunk4_4_checked, root7Node126Step1Chunk4_5_checked, root7Node126Step1Chunk5_0_checked, root7Node126Step1Chunk5_1_checked, root7Node126Step1Chunk5_2_checked, root7Node126Step1Chunk5_3_checked, root7Node126Step1Chunk5_4_checked, root7Node126Step1Chunk5_5_checked, root7Node126Step1Chunk6_0_checked, root7Node126Step1Chunk6_1_checked, root7Node126Step1Chunk6_2_checked, root7Node126Step1Chunk6_3_checked, root7Node126Step1Chunk6_4_checked, root7Node126Step1Chunk6_5_checked, root7Node126Step1Chunk7_0_checked, root7Node126Step1Chunk7_1_checked, root7Node126Step1Chunk7_2_checked, root7Node126Step1Chunk7_3_checked, root7Node126Step1Chunk7_4_checked, root7Node126Step1Chunk7_5_checked, root7Node126Step1Chunk8_0_checked, root7Node126Step1Chunk8_1_checked, root7Node126Step1Chunk8_2_checked, root7Node126Step1Chunk8_3_checked, root7Node126Step1Chunk8_4_checked, root7Node126Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node126Step1_checked :
    checkReplacement table56 root7Node126Domains0 root7Node126Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node126Domains0 root7Node126Domains1
    root7Node126Domains0Fast root7Node126Domains1Fast
    root7Node126Domains0_fast_eq root7Node126Domains1_fast_eq
    root7Node126Step1Narrowing_checked (by decide)
theorem root7Node126Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node126Domains1 (.output 62) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
