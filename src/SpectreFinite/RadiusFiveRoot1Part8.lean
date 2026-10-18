module

public import SpectreFinite.RadiusFiveRoot1Part7
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable41
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node19Domains0 : Domains 91 State := restrict root1Node15Domains3 20 (8,1)
def root1Node19Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(3,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(2,3)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(4,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(5,3)]
  | 71 => some [(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(1,1)]
  | 86 => some [(8,1)]
  | 87 => some [(6,5)]
  | 88 => some [(0,4)]
  | 89 => some [(1,4),(3,4)]
  | _ => some [(0,5),(6,3)]
theorem root1Node19Domains0_fast_eq : root1Node19Domains0 = expandDomains root1Node19Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node19Domains0 v = expandDomains root1Node19Domains0Fast v from by decide) v
def root1Node20Domains0 : Domains 91 State := restrict root1Node19Domains0 84 (5,5)
def root1Node20Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(3,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(2,3)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(4,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(5,3)]
  | 71 => some [(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(5,5)]
  | 85 => some [(1,1)]
  | 86 => some [(8,1)]
  | 87 => some [(6,5)]
  | 88 => some [(0,4)]
  | 89 => some [(1,4),(3,4)]
  | _ => some [(0,5),(6,3)]
theorem root1Node20Domains0_fast_eq : root1Node20Domains0 = expandDomains root1Node20Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node20Domains0 v = expandDomains root1Node20Domains0Fast v from by decide) v
def root1Node20Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(8,3)]
  | 5 => [(8,5)]
  | 6 => [(0,4)]
  | 7 => [(3,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,0)]
  | 14 => [(2,3)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(8,1)]
  | 21 => [(4,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(0,3)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(4,4)]
  | 40 => [(8,0)]
  | 41 => [(7,3)]
  | 42 => [(4,2)]
  | 43 => [(5,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(7,1)]
  | 50 => [(1,5)]
  | 51 => [(6,4)]
  | 52 => [(1,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3)]
  | 55 => [(8,2)]
  | 56 => [(8,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(0,3)]
  | 62 => [(8,1)]
  | 63 => [(6,5)]
  | 64 => [(0,4)]
  | 65 => [(5,4)]
  | 66 => [(6,4)]
  | 67 => [(1,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0)]
  | 70 => [(5,3)]
  | 71 => [(8,5)]
  | 72 => [(7,0)]
  | 73 => [(4,3)]
  | 74 => [(7,5)]
  | 75 => [(0,3)]
  | 76 => [(8,1)]
  | 77 => [(1,5)]
  | 78 => [(6,3)]
  | 79 => [(7,2)]
  | 80 => [(7,4)]
  | 81 => [(1,3)]
  | 82 => [(4,2)]
  | 83 => [(5,3)]
  | 84 => [(5,5)]
  | 85 => [(1,1)]
  | 86 => [(8,1)]
  | 87 => [(6,5)]
  | 88 => [(0,4)]
  | 89 => [(1,4)]
  | _ => [(0,5)]
def root1Node20Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(3,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(2,3)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(4,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(5,3)]
  | 71 => some [(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(5,5)]
  | 85 => some [(1,1)]
  | 86 => some [(8,1)]
  | 87 => some [(6,5)]
  | 88 => some [(0,4)]
  | 89 => some [(1,4)]
  | _ => some [(0,5)]
theorem root1Node20Domains1_fast_eq : root1Node20Domains1 = expandDomains root1Node20Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node20Domains1 v = expandDomains root1Node20Domains1Fast v from by decide) v
theorem root1Node20Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq (by decide)
theorem root1Node20Step1Narrowing_checked :
    checkNarrowing table56 root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root1Node20Domains0 root1Node20Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node20Step1Chunk0_0_checked, root1Node20Step1Chunk0_1_checked, root1Node20Step1Chunk0_2_checked, root1Node20Step1Chunk0_3_checked, root1Node20Step1Chunk0_4_checked, root1Node20Step1Chunk0_5_checked, root1Node20Step1Chunk1_0_checked, root1Node20Step1Chunk1_1_checked, root1Node20Step1Chunk1_2_checked, root1Node20Step1Chunk1_3_checked, root1Node20Step1Chunk1_4_checked, root1Node20Step1Chunk1_5_checked, root1Node20Step1Chunk2_0_checked, root1Node20Step1Chunk2_1_checked, root1Node20Step1Chunk2_2_checked, root1Node20Step1Chunk2_3_checked, root1Node20Step1Chunk2_4_checked, root1Node20Step1Chunk2_5_checked, root1Node20Step1Chunk3_0_checked, root1Node20Step1Chunk3_1_checked, root1Node20Step1Chunk3_2_checked, root1Node20Step1Chunk3_3_checked, root1Node20Step1Chunk3_4_checked, root1Node20Step1Chunk3_5_checked, root1Node20Step1Chunk4_0_checked, root1Node20Step1Chunk4_1_checked, root1Node20Step1Chunk4_2_checked, root1Node20Step1Chunk4_3_checked, root1Node20Step1Chunk4_4_checked, root1Node20Step1Chunk4_5_checked, root1Node20Step1Chunk5_0_checked, root1Node20Step1Chunk5_1_checked, root1Node20Step1Chunk5_2_checked, root1Node20Step1Chunk5_3_checked, root1Node20Step1Chunk5_4_checked, root1Node20Step1Chunk5_5_checked, root1Node20Step1Chunk6_0_checked, root1Node20Step1Chunk6_1_checked, root1Node20Step1Chunk6_2_checked, root1Node20Step1Chunk6_3_checked, root1Node20Step1Chunk6_4_checked, root1Node20Step1Chunk6_5_checked, root1Node20Step1Chunk7_0_checked, root1Node20Step1Chunk7_1_checked, root1Node20Step1Chunk7_2_checked, root1Node20Step1Chunk7_3_checked, root1Node20Step1Chunk7_4_checked, root1Node20Step1Chunk7_5_checked, root1Node20Step1Chunk8_0_checked, root1Node20Step1Chunk8_1_checked, root1Node20Step1Chunk8_2_checked, root1Node20Step1Chunk8_3_checked, root1Node20Step1Chunk8_4_checked, root1Node20Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node20Step1_checked :
    checkReplacement table56 root1Node20Domains0 root1Node20Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node20Domains0 root1Node20Domains1
    root1Node20Domains0Fast root1Node20Domains1Fast
    root1Node20Domains0_fast_eq root1Node20Domains1_fast_eq
    root1Node20Step1Narrowing_checked (by decide)
theorem root1Node20Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node20Domains1 (.output 8) = true := by decide
def root1Node21Domains0 : Domains 91 State := restrict root1Node19Domains0 84 (8,5)
def root1Node21Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(3,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(2,3)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(4,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(5,3)]
  | 71 => some [(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(8,5)]
  | 85 => some [(1,1)]
  | 86 => some [(8,1)]
  | 87 => some [(6,5)]
  | 88 => some [(0,4)]
  | 89 => some [(1,4),(3,4)]
  | _ => some [(0,5),(6,3)]
theorem root1Node21Domains0_fast_eq : root1Node21Domains0 = expandDomains root1Node21Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node21Domains0 v = expandDomains root1Node21Domains0Fast v from by decide) v
def root1Node21Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(8,3)]
  | 5 => [(8,5)]
  | 6 => [(0,4)]
  | 7 => [(3,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,0)]
  | 14 => [(2,3)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(8,1)]
  | 21 => [(4,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(0,3)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(4,4)]
  | 40 => [(8,0)]
  | 41 => [(7,3)]
  | 42 => [(4,2)]
  | 43 => [(5,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(7,1)]
  | 50 => [(1,5)]
  | 51 => [(6,4)]
  | 52 => [(1,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3)]
  | 55 => [(8,2)]
  | 56 => [(8,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0)]
  | 60 => [(4,5)]
  | 61 => [(0,3)]
  | 62 => [(8,1)]
  | 63 => [(6,5)]
  | 64 => [(0,4)]
  | 65 => [(5,4)]
  | 66 => [(6,4)]
  | 67 => [(1,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0)]
  | 70 => [(5,3)]
  | 71 => [(8,5)]
  | 72 => [(7,0)]
  | 73 => [(4,3)]
  | 74 => [(7,5)]
  | 75 => [(0,3)]
  | 76 => [(8,1)]
  | 77 => [(1,5)]
  | 78 => [(6,3)]
  | 79 => [(7,2)]
  | 80 => [(7,4)]
  | 81 => [(1,3)]
  | 82 => [(4,2)]
  | 83 => [(5,3)]
  | 84 => [(8,5)]
  | 85 => [(1,1)]
  | 86 => [(8,1)]
  | 87 => [(6,5)]
  | 88 => [(0,4)]
  | 89 => [(3,4)]
  | _ => [(6,3)]
def root1Node21Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(3,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(2,3)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(4,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(4,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(4,2)]
  | 43 => some [(5,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3)]
  | 55 => some [(8,2)]
  | 56 => some [(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0)]
  | 60 => some [(4,5)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(6,5)]
  | 64 => some [(0,4)]
  | 65 => some [(5,4)]
  | 66 => some [(6,4)]
  | 67 => some [(1,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0)]
  | 70 => some [(5,3)]
  | 71 => some [(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(4,3)]
  | 74 => some [(7,5)]
  | 75 => some [(0,3)]
  | 76 => some [(8,1)]
  | 77 => some [(1,5)]
  | 78 => some [(6,3)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3)]
  | 82 => some [(4,2)]
  | 83 => some [(5,3)]
  | 84 => some [(8,5)]
  | 85 => some [(1,1)]
  | 86 => some [(8,1)]
  | 87 => some [(6,5)]
  | 88 => some [(0,4)]
  | 89 => some [(3,4)]
  | _ => some [(6,3)]
theorem root1Node21Domains1_fast_eq : root1Node21Domains1 = expandDomains root1Node21Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node21Domains1 v = expandDomains root1Node21Domains1Fast v from by decide) v
theorem root1Node21Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq (by decide)
theorem root1Node21Step1Narrowing_checked :
    checkNarrowing table56 root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root1Node21Domains0 root1Node21Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node21Step1Chunk0_0_checked, root1Node21Step1Chunk0_1_checked, root1Node21Step1Chunk0_2_checked, root1Node21Step1Chunk0_3_checked, root1Node21Step1Chunk0_4_checked, root1Node21Step1Chunk0_5_checked, root1Node21Step1Chunk1_0_checked, root1Node21Step1Chunk1_1_checked, root1Node21Step1Chunk1_2_checked, root1Node21Step1Chunk1_3_checked, root1Node21Step1Chunk1_4_checked, root1Node21Step1Chunk1_5_checked, root1Node21Step1Chunk2_0_checked, root1Node21Step1Chunk2_1_checked, root1Node21Step1Chunk2_2_checked, root1Node21Step1Chunk2_3_checked, root1Node21Step1Chunk2_4_checked, root1Node21Step1Chunk2_5_checked, root1Node21Step1Chunk3_0_checked, root1Node21Step1Chunk3_1_checked, root1Node21Step1Chunk3_2_checked, root1Node21Step1Chunk3_3_checked, root1Node21Step1Chunk3_4_checked, root1Node21Step1Chunk3_5_checked, root1Node21Step1Chunk4_0_checked, root1Node21Step1Chunk4_1_checked, root1Node21Step1Chunk4_2_checked, root1Node21Step1Chunk4_3_checked, root1Node21Step1Chunk4_4_checked, root1Node21Step1Chunk4_5_checked, root1Node21Step1Chunk5_0_checked, root1Node21Step1Chunk5_1_checked, root1Node21Step1Chunk5_2_checked, root1Node21Step1Chunk5_3_checked, root1Node21Step1Chunk5_4_checked, root1Node21Step1Chunk5_5_checked, root1Node21Step1Chunk6_0_checked, root1Node21Step1Chunk6_1_checked, root1Node21Step1Chunk6_2_checked, root1Node21Step1Chunk6_3_checked, root1Node21Step1Chunk6_4_checked, root1Node21Step1Chunk6_5_checked, root1Node21Step1Chunk7_0_checked, root1Node21Step1Chunk7_1_checked, root1Node21Step1Chunk7_2_checked, root1Node21Step1Chunk7_3_checked, root1Node21Step1Chunk7_4_checked, root1Node21Step1Chunk7_5_checked, root1Node21Step1Chunk8_0_checked, root1Node21Step1Chunk8_1_checked, root1Node21Step1Chunk8_2_checked, root1Node21Step1Chunk8_3_checked, root1Node21Step1Chunk8_4_checked, root1Node21Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node21Step1_checked :
    checkReplacement table56 root1Node21Domains0 root1Node21Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node21Domains0 root1Node21Domains1
    root1Node21Domains0Fast root1Node21Domains1Fast
    root1Node21Domains0_fast_eq root1Node21Domains1_fast_eq
    root1Node21Step1Narrowing_checked (by decide)
theorem root1Node21Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node21Domains1 (.output 9) = true := by decide
def root1Node22Domains0 : Domains 91 State := restrict root1Node6Domains2 6 (6,2)
def root1Node22Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(8,5)]
  | 6 => some [(6,2)]
  | 7 => some [(3,4),(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(1,0),(7,0)]
  | 14 => some [(2,1),(2,3)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1),(5,1),(8,1)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0),(6,4)]
  | 23 => some [(1,2),(3,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3),(8,3)]
  | 29 => some [(5,2),(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5),(7,5)]
  | 32 => some [(0,3),(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(1,4),(6,4)]
  | 38 => some [(0,5),(1,2)]
  | 39 => some [(4,4),(8,4)]
  | 40 => some [(5,0),(8,0)]
  | 41 => some [(4,5),(7,3)]
  | 42 => some [(4,2),(7,0)]
  | 43 => some [(5,3),(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3),(6,0)]
  | 49 => some [(7,1),(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(0,0),(6,4)]
  | 52 => some [(1,2),(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2),(8,2)]
  | 59 => some [(5,0),(5,3)]
  | 60 => some [(4,5),(8,5)]
  | 61 => some [(0,3),(6,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(0,2),(6,5)]
  | 64 => some [(0,4),(1,1)]
  | 65 => some [(5,1),(5,4)]
  | 66 => some [(0,1),(6,4)]
  | 67 => some [(1,2),(6,2)]
  | 68 => some [(7,4),(8,4)]
  | 69 => some [(0,0),(6,3)]
  | 70 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 71 => some [(5,2),(5,5),(8,5)]
  | 72 => some [(7,0),(8,0)]
  | 73 => some [(4,3),(8,3)]
  | 74 => some [(3,5),(5,5),(7,5)]
  | 75 => some [(0,3),(1,0)]
  | 76 => some [(2,1),(4,1),(8,1)]
  | 77 => some [(0,2),(1,5)]
  | 78 => some [(0,4),(0,5),(6,2),(6,3)]
  | 79 => some [(4,4),(5,4),(7,2),(8,4)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(1,3),(6,3)]
  | 82 => some [(2,2),(2,4),(4,2),(4,4)]
  | 83 => some [(0,0),(1,3),(3,3),(5,3)]
  | 84 => some [(3,2),(5,2),(5,5),(8,5)]
  | 85 => some [(1,1),(4,3),(7,1)]
  | 86 => some [(4,1),(7,5),(8,1)]
  | 87 => some [(0,2),(6,0),(6,5)]
  | 88 => some [(0,4),(1,1),(7,1)]
  | 89 => some [(0,1),(1,4),(1,5),(3,4),(6,5)]
  | _ => some [(0,4),(0,5),(6,1),(6,2),(6,3)]
theorem root1Node22Domains0_fast_eq : root1Node22Domains0 = expandDomains root1Node22Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node22Domains0 v = expandDomains root1Node22Domains0Fast v from by decide) v
def root1Node22Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2)]
  | 1 => [(5,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(8,3)]
  | 5 => [(8,5)]
  | 6 => [(6,2)]
  | 7 => [(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(1,0)]
  | 14 => [(2,1)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(4,1),(5,1),(8,1)]
  | 21 => [(4,4)]
  | 22 => [(0,0)]
  | 23 => [(3,2)]
  | 24 => [(4,0)]
  | 25 => [(7,3)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3),(8,3)]
  | 29 => [(5,2),(5,5)]
  | 30 => [(7,1)]
  | 31 => [(1,5)]
  | 32 => [(6,1)]
  | 33 => [(5,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(1,4),(6,4)]
  | 38 => [(0,5),(1,2)]
  | 39 => [(4,4),(8,4)]
  | 40 => [(5,0)]
  | 41 => [(4,5)]
  | 42 => [(7,0)]
  | 43 => [(8,3)]
  | 44 => [(8,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(0,3),(6,0)]
  | 49 => [(7,1),(8,1)]
  | 50 => [(1,5)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3),(6,3)]
  | 55 => [(7,2),(8,2)]
  | 56 => [(4,0),(8,0)]
  | 57 => [(7,3)]
  | 58 => [(4,2),(8,2)]
  | 59 => [(5,0),(5,3)]
  | 60 => [(4,5),(8,5)]
  | 61 => [(6,1)]
  | 62 => [(4,1),(8,1)]
  | 63 => [(0,2),(6,5)]
  | 64 => [(0,4),(1,1)]
  | 65 => [(5,1),(5,4)]
  | 66 => [(0,1),(6,4)]
  | 67 => [(1,2),(6,2)]
  | 68 => [(7,4),(8,4)]
  | 69 => [(0,0),(6,3)]
  | 70 => [(7,3),(8,3)]
  | 71 => [(5,2),(5,5),(8,5)]
  | 72 => [(7,0),(8,0)]
  | 73 => [(4,3),(8,3)]
  | 74 => [(3,5),(5,5),(7,5)]
  | 75 => [(0,3),(1,0)]
  | 76 => [(2,1),(4,1),(8,1)]
  | 77 => [(0,2),(1,5)]
  | 78 => [(0,5),(6,2),(6,3)]
  | 79 => [(4,4),(7,2),(8,4)]
  | 80 => [(1,4),(7,4)]
  | 81 => [(0,5),(1,3),(6,3)]
  | 82 => [(2,2),(2,4),(4,2),(4,4)]
  | 83 => [(0,0),(1,3),(3,3),(5,3)]
  | 84 => [(3,2),(5,2),(5,5),(8,5)]
  | 85 => [(1,1),(4,3),(7,1)]
  | 86 => [(4,1),(7,5),(8,1)]
  | 87 => [(0,2),(6,0),(6,5)]
  | 88 => [(0,4),(1,1),(7,1)]
  | 89 => [(0,1),(1,4),(1,5),(3,4),(6,5)]
  | _ => [(0,4),(0,5),(6,1),(6,2),(6,3)]
def root1Node22Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2)]
  | 1 => some [(5,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(8,3)]
  | 5 => some [(8,5)]
  | 6 => some [(6,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(1,0)]
  | 14 => some [(2,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1),(5,1),(8,1)]
  | 21 => some [(4,4)]
  | 22 => some [(0,0)]
  | 23 => some [(3,2)]
  | 24 => some [(4,0)]
  | 25 => some [(7,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3),(8,3)]
  | 29 => some [(5,2),(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(1,5)]
  | 32 => some [(6,1)]
  | 33 => some [(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(1,4),(6,4)]
  | 38 => some [(0,5),(1,2)]
  | 39 => some [(4,4),(8,4)]
  | 40 => some [(5,0)]
  | 41 => some [(4,5)]
  | 42 => some [(7,0)]
  | 43 => some [(8,3)]
  | 44 => some [(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3),(6,0)]
  | 49 => some [(7,1),(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(8,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2),(8,2)]
  | 59 => some [(5,0),(5,3)]
  | 60 => some [(4,5),(8,5)]
  | 61 => some [(6,1)]
  | 62 => some [(4,1),(8,1)]
  | 63 => some [(0,2),(6,5)]
  | 64 => some [(0,4),(1,1)]
  | 65 => some [(5,1),(5,4)]
  | 66 => some [(0,1),(6,4)]
  | 67 => some [(1,2),(6,2)]
  | 68 => some [(7,4),(8,4)]
  | 69 => some [(0,0),(6,3)]
  | 70 => some [(7,3),(8,3)]
  | 71 => some [(5,2),(5,5),(8,5)]
  | 72 => some [(7,0),(8,0)]
  | 73 => some [(4,3),(8,3)]
  | 74 => some [(3,5),(5,5),(7,5)]
  | 75 => some [(0,3),(1,0)]
  | 76 => some [(2,1),(4,1),(8,1)]
  | 77 => some [(0,2),(1,5)]
  | 78 => some [(0,5),(6,2),(6,3)]
  | 79 => some [(4,4),(7,2),(8,4)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(1,3),(6,3)]
  | 82 => some [(2,2),(2,4),(4,2),(4,4)]
  | 83 => some [(0,0),(1,3),(3,3),(5,3)]
  | 84 => some [(3,2),(5,2),(5,5),(8,5)]
  | 85 => some [(1,1),(4,3),(7,1)]
  | 86 => some [(4,1),(7,5),(8,1)]
  | 87 => some [(0,2),(6,0),(6,5)]
  | 88 => some [(0,4),(1,1),(7,1)]
  | 89 => some [(0,1),(1,4),(1,5),(3,4),(6,5)]
  | _ => some [(0,4),(0,5),(6,1),(6,2),(6,3)]
theorem root1Node22Domains1_fast_eq : root1Node22Domains1 = expandDomains root1Node22Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node22Domains1 v = expandDomains root1Node22Domains1Fast v from by decide) v
theorem root1Node22Step1Chunk0_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows0_0⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk0_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows0_1⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk0_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows0_2⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk0_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows0_3⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk0_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows0_4⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk0_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows0_5⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk1_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows1_0⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk1_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows1_1⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk1_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows1_2⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk1_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows1_3⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk1_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows1_4⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk1_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows1_5⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk2_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows2_0⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk2_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows2_1⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk2_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows2_2⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk2_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows2_3⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk2_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows2_4⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk2_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows2_5⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk3_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows3_0⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk3_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows3_1⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk3_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows3_2⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk3_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows3_3⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk3_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows3_4⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk3_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows3_5⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk4_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows4_0⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk4_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows4_1⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk4_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows4_2⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk4_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows4_3⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk4_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows4_4⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk4_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows4_5⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk5_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows5_0⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk5_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows5_1⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk5_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows5_2⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk5_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows5_3⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk5_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows5_4⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk5_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows5_5⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk6_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows6_0⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk6_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows6_1⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk6_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows6_2⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk6_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows6_3⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk6_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows6_4⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk6_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows6_5⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk7_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows7_0⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk7_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows7_1⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk7_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows7_2⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk7_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows7_3⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk7_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows7_4⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk7_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows7_5⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk8_0_checked :
    checkNarrowing ⟨table41Scope, table41Rows8_0⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk8_1_checked :
    checkNarrowing ⟨table41Scope, table41Rows8_1⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk8_2_checked :
    checkNarrowing ⟨table41Scope, table41Rows8_2⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk8_3_checked :
    checkNarrowing ⟨table41Scope, table41Rows8_3⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk8_4_checked :
    checkNarrowing ⟨table41Scope, table41Rows8_4⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Chunk8_5_checked :
    checkNarrowing ⟨table41Scope, table41Rows8_5⟩
      root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq (by decide)
theorem root1Node22Step1Narrowing_checked :
    checkNarrowing table41 root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkNarrowing_flatten table41Scope [table41Rows0_0,table41Rows0_1,table41Rows0_2,table41Rows0_3,table41Rows0_4,table41Rows0_5,table41Rows1_0,table41Rows1_1,table41Rows1_2,table41Rows1_3,table41Rows1_4,table41Rows1_5,table41Rows2_0,table41Rows2_1,table41Rows2_2,table41Rows2_3,table41Rows2_4,table41Rows2_5,table41Rows3_0,table41Rows3_1,table41Rows3_2,table41Rows3_3,table41Rows3_4,table41Rows3_5,table41Rows4_0,table41Rows4_1,table41Rows4_2,table41Rows4_3,table41Rows4_4,table41Rows4_5,table41Rows5_0,table41Rows5_1,table41Rows5_2,table41Rows5_3,table41Rows5_4,table41Rows5_5,table41Rows6_0,table41Rows6_1,table41Rows6_2,table41Rows6_3,table41Rows6_4,table41Rows6_5,table41Rows7_0,table41Rows7_1,table41Rows7_2,table41Rows7_3,table41Rows7_4,table41Rows7_5,table41Rows8_0,table41Rows8_1,table41Rows8_2,table41Rows8_3,table41Rows8_4,table41Rows8_5]
    root1Node22Domains0 root1Node22Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node22Step1Chunk0_0_checked, root1Node22Step1Chunk0_1_checked, root1Node22Step1Chunk0_2_checked, root1Node22Step1Chunk0_3_checked, root1Node22Step1Chunk0_4_checked, root1Node22Step1Chunk0_5_checked, root1Node22Step1Chunk1_0_checked, root1Node22Step1Chunk1_1_checked, root1Node22Step1Chunk1_2_checked, root1Node22Step1Chunk1_3_checked, root1Node22Step1Chunk1_4_checked, root1Node22Step1Chunk1_5_checked, root1Node22Step1Chunk2_0_checked, root1Node22Step1Chunk2_1_checked, root1Node22Step1Chunk2_2_checked, root1Node22Step1Chunk2_3_checked, root1Node22Step1Chunk2_4_checked, root1Node22Step1Chunk2_5_checked, root1Node22Step1Chunk3_0_checked, root1Node22Step1Chunk3_1_checked, root1Node22Step1Chunk3_2_checked, root1Node22Step1Chunk3_3_checked, root1Node22Step1Chunk3_4_checked, root1Node22Step1Chunk3_5_checked, root1Node22Step1Chunk4_0_checked, root1Node22Step1Chunk4_1_checked, root1Node22Step1Chunk4_2_checked, root1Node22Step1Chunk4_3_checked, root1Node22Step1Chunk4_4_checked, root1Node22Step1Chunk4_5_checked, root1Node22Step1Chunk5_0_checked, root1Node22Step1Chunk5_1_checked, root1Node22Step1Chunk5_2_checked, root1Node22Step1Chunk5_3_checked, root1Node22Step1Chunk5_4_checked, root1Node22Step1Chunk5_5_checked, root1Node22Step1Chunk6_0_checked, root1Node22Step1Chunk6_1_checked, root1Node22Step1Chunk6_2_checked, root1Node22Step1Chunk6_3_checked, root1Node22Step1Chunk6_4_checked, root1Node22Step1Chunk6_5_checked, root1Node22Step1Chunk7_0_checked, root1Node22Step1Chunk7_1_checked, root1Node22Step1Chunk7_2_checked, root1Node22Step1Chunk7_3_checked, root1Node22Step1Chunk7_4_checked, root1Node22Step1Chunk7_5_checked, root1Node22Step1Chunk8_0_checked, root1Node22Step1Chunk8_1_checked, root1Node22Step1Chunk8_2_checked, root1Node22Step1Chunk8_3_checked, root1Node22Step1Chunk8_4_checked, root1Node22Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node22Step1_checked :
    checkReplacement table41 root1Node22Domains0 root1Node22Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node22Domains0 root1Node22Domains1
    root1Node22Domains0Fast root1Node22Domains1Fast
    root1Node22Domains0_fast_eq root1Node22Domains1_fast_eq
    root1Node22Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
