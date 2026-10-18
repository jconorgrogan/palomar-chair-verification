module

public import SpectreFinite.RadiusFiveRoot7Part16
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node41Domains0 : Domains 91 State := restrict root7Node40Domains4 5 (3,2)
def root7Node41Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(1,4)]
  | 2 => some [(0,5)]
  | 3 => some [(4,4)]
  | 4 => some [(0,0)]
  | 5 => some [(3,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(6,0)]
  | 9 => some [(7,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(5,1)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,3)]
  | 31 => some [(8,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(5,4)]
  | 40 => some [(7,4)]
  | 41 => some [(1,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(7,0)]
  | 49 => some [(4,3)]
  | 50 => some [(7,5)]
  | 51 => some [(6,5)]
  | 52 => some [(0,4)]
  | 53 => some [(5,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(6,3)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | 60 => some [(1,3),(6,3)]
  | 61 => some [(7,0)]
  | 62 => some [(4,3)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(4,1)]
  | 66 => some [(0,2)]
  | 67 => some [(1,1)]
  | 68 => some [(4,1),(8,1)]
  | 69 => some [(0,2),(6,5)]
  | 70 => some [(1,4)]
  | 71 => some [(0,5)]
  | 72 => some [(2,0)]
  | 73 => some [(7,3)]
  | 74 => some [(5,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3),(8,3)]
  | 77 => some [(5,2),(5,5)]
  | 78 => some [(6,0)]
  | 79 => some [(3,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(1,4),(6,4)]
  | 84 => some [(0,5),(1,2)]
  | 85 => some [(5,0)]
  | 86 => some [(4,5)]
  | 87 => some [(1,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(0,3),(6,0)]
theorem root7Node41Domains0_fast_eq : root7Node41Domains0 = expandDomains root7Node41Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node41Domains0 v = expandDomains root7Node41Domains0Fast v from by decide) v
def root7Node42Domains0 : Domains 91 State := restrict root7Node41Domains0 60 (1,3)
def root7Node42Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(1,4)]
  | 2 => some [(0,5)]
  | 3 => some [(4,4)]
  | 4 => some [(0,0)]
  | 5 => some [(3,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(6,0)]
  | 9 => some [(7,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(5,1)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,3)]
  | 31 => some [(8,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(5,4)]
  | 40 => some [(7,4)]
  | 41 => some [(1,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(7,0)]
  | 49 => some [(4,3)]
  | 50 => some [(7,5)]
  | 51 => some [(6,5)]
  | 52 => some [(0,4)]
  | 53 => some [(5,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(6,3)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | 60 => some [(1,3)]
  | 61 => some [(7,0)]
  | 62 => some [(4,3)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(4,1)]
  | 66 => some [(0,2)]
  | 67 => some [(1,1)]
  | 68 => some [(4,1),(8,1)]
  | 69 => some [(0,2),(6,5)]
  | 70 => some [(1,4)]
  | 71 => some [(0,5)]
  | 72 => some [(2,0)]
  | 73 => some [(7,3)]
  | 74 => some [(5,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3),(8,3)]
  | 77 => some [(5,2),(5,5)]
  | 78 => some [(6,0)]
  | 79 => some [(3,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(1,4),(6,4)]
  | 84 => some [(0,5),(1,2)]
  | 85 => some [(5,0)]
  | 86 => some [(4,5)]
  | 87 => some [(1,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(0,3),(6,0)]
theorem root7Node42Domains0_fast_eq : root7Node42Domains0 = expandDomains root7Node42Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node42Domains0 v = expandDomains root7Node42Domains0Fast v from by decide) v
def root7Node42Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4)]
  | 1 => [(1,4)]
  | 2 => [(0,5)]
  | 3 => [(4,4)]
  | 4 => [(0,0)]
  | 5 => [(3,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(6,0)]
  | 9 => [(7,1)]
  | 10 => [(1,5)]
  | 11 => [(6,1)]
  | 12 => [(5,1)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(5,1)]
  | 22 => [(0,1)]
  | 23 => [(6,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(8,3)]
  | 31 => [(8,5)]
  | 32 => [(1,0)]
  | 33 => [(7,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(8,1)]
  | 37 => [(6,5)]
  | 38 => [(0,4)]
  | 39 => [(5,4)]
  | 40 => [(7,4)]
  | 41 => [(1,3)]
  | 42 => [(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(8,5)]
  | 48 => [(7,0)]
  | 49 => [(4,3)]
  | 50 => [(7,5)]
  | 51 => [(6,5)]
  | 52 => [(0,4)]
  | 53 => [(5,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(6,3)]
  | 58 => [(7,2)]
  | 59 => [(7,4)]
  | 60 => [(1,3)]
  | 61 => [(7,0)]
  | 62 => [(4,3)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(4,1)]
  | 66 => [(0,2)]
  | 67 => [(1,1)]
  | 68 => [(8,1)]
  | 69 => [(6,5)]
  | 70 => [(1,4)]
  | 71 => [(0,5)]
  | 72 => [(2,0)]
  | 73 => [(7,3)]
  | 74 => [(5,2)]
  | 75 => [(8,0)]
  | 76 => [(8,3)]
  | 77 => [(5,5)]
  | 78 => [(6,0)]
  | 79 => [(3,1)]
  | 80 => [(0,1)]
  | 81 => [(6,2)]
  | 82 => [(8,4)]
  | 83 => [(1,4)]
  | 84 => [(0,5)]
  | 85 => [(5,0)]
  | 86 => [(4,5)]
  | 87 => [(1,0)]
  | 88 => [(7,1)]
  | 89 => [(7,5)]
  | _ => [(6,0)]
def root7Node42Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(1,4)]
  | 2 => some [(0,5)]
  | 3 => some [(4,4)]
  | 4 => some [(0,0)]
  | 5 => some [(3,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(6,0)]
  | 9 => some [(7,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(5,1)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,3)]
  | 31 => some [(8,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(5,4)]
  | 40 => some [(7,4)]
  | 41 => some [(1,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(7,0)]
  | 49 => some [(4,3)]
  | 50 => some [(7,5)]
  | 51 => some [(6,5)]
  | 52 => some [(0,4)]
  | 53 => some [(5,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(6,3)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | 60 => some [(1,3)]
  | 61 => some [(7,0)]
  | 62 => some [(4,3)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(4,1)]
  | 66 => some [(0,2)]
  | 67 => some [(1,1)]
  | 68 => some [(8,1)]
  | 69 => some [(6,5)]
  | 70 => some [(1,4)]
  | 71 => some [(0,5)]
  | 72 => some [(2,0)]
  | 73 => some [(7,3)]
  | 74 => some [(5,2)]
  | 75 => some [(8,0)]
  | 76 => some [(8,3)]
  | 77 => some [(5,5)]
  | 78 => some [(6,0)]
  | 79 => some [(3,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(1,4)]
  | 84 => some [(0,5)]
  | 85 => some [(5,0)]
  | 86 => some [(4,5)]
  | 87 => some [(1,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(6,0)]
theorem root7Node42Domains1_fast_eq : root7Node42Domains1 = expandDomains root7Node42Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node42Domains1 v = expandDomains root7Node42Domains1Fast v from by decide) v
theorem root7Node42Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq (by decide)
theorem root7Node42Step1Narrowing_checked :
    checkNarrowing table56 root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root7Node42Domains0 root7Node42Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node42Step1Chunk0_0_checked, root7Node42Step1Chunk0_1_checked, root7Node42Step1Chunk0_2_checked, root7Node42Step1Chunk0_3_checked, root7Node42Step1Chunk0_4_checked, root7Node42Step1Chunk0_5_checked, root7Node42Step1Chunk1_0_checked, root7Node42Step1Chunk1_1_checked, root7Node42Step1Chunk1_2_checked, root7Node42Step1Chunk1_3_checked, root7Node42Step1Chunk1_4_checked, root7Node42Step1Chunk1_5_checked, root7Node42Step1Chunk2_0_checked, root7Node42Step1Chunk2_1_checked, root7Node42Step1Chunk2_2_checked, root7Node42Step1Chunk2_3_checked, root7Node42Step1Chunk2_4_checked, root7Node42Step1Chunk2_5_checked, root7Node42Step1Chunk3_0_checked, root7Node42Step1Chunk3_1_checked, root7Node42Step1Chunk3_2_checked, root7Node42Step1Chunk3_3_checked, root7Node42Step1Chunk3_4_checked, root7Node42Step1Chunk3_5_checked, root7Node42Step1Chunk4_0_checked, root7Node42Step1Chunk4_1_checked, root7Node42Step1Chunk4_2_checked, root7Node42Step1Chunk4_3_checked, root7Node42Step1Chunk4_4_checked, root7Node42Step1Chunk4_5_checked, root7Node42Step1Chunk5_0_checked, root7Node42Step1Chunk5_1_checked, root7Node42Step1Chunk5_2_checked, root7Node42Step1Chunk5_3_checked, root7Node42Step1Chunk5_4_checked, root7Node42Step1Chunk5_5_checked, root7Node42Step1Chunk6_0_checked, root7Node42Step1Chunk6_1_checked, root7Node42Step1Chunk6_2_checked, root7Node42Step1Chunk6_3_checked, root7Node42Step1Chunk6_4_checked, root7Node42Step1Chunk6_5_checked, root7Node42Step1Chunk7_0_checked, root7Node42Step1Chunk7_1_checked, root7Node42Step1Chunk7_2_checked, root7Node42Step1Chunk7_3_checked, root7Node42Step1Chunk7_4_checked, root7Node42Step1Chunk7_5_checked, root7Node42Step1Chunk8_0_checked, root7Node42Step1Chunk8_1_checked, root7Node42Step1Chunk8_2_checked, root7Node42Step1Chunk8_3_checked, root7Node42Step1Chunk8_4_checked, root7Node42Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node42Step1_checked :
    checkReplacement table56 root7Node42Domains0 root7Node42Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node42Domains0 root7Node42Domains1
    root7Node42Domains0Fast root7Node42Domains1Fast
    root7Node42Domains0_fast_eq root7Node42Domains1_fast_eq
    root7Node42Step1Narrowing_checked (by decide)
theorem root7Node42Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node42Domains1 (.output 18) = true := by decide
def root7Node43Domains0 : Domains 91 State := restrict root7Node41Domains0 60 (6,3)
def root7Node43Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(1,4)]
  | 2 => some [(0,5)]
  | 3 => some [(4,4)]
  | 4 => some [(0,0)]
  | 5 => some [(3,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(6,0)]
  | 9 => some [(7,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(5,1)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,3)]
  | 31 => some [(8,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(5,4)]
  | 40 => some [(7,4)]
  | 41 => some [(1,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(7,0)]
  | 49 => some [(4,3)]
  | 50 => some [(7,5)]
  | 51 => some [(6,5)]
  | 52 => some [(0,4)]
  | 53 => some [(5,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(6,3)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | 60 => some [(6,3)]
  | 61 => some [(7,0)]
  | 62 => some [(4,3)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(4,1)]
  | 66 => some [(0,2)]
  | 67 => some [(1,1)]
  | 68 => some [(4,1),(8,1)]
  | 69 => some [(0,2),(6,5)]
  | 70 => some [(1,4)]
  | 71 => some [(0,5)]
  | 72 => some [(2,0)]
  | 73 => some [(7,3)]
  | 74 => some [(5,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3),(8,3)]
  | 77 => some [(5,2),(5,5)]
  | 78 => some [(6,0)]
  | 79 => some [(3,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(1,4),(6,4)]
  | 84 => some [(0,5),(1,2)]
  | 85 => some [(5,0)]
  | 86 => some [(4,5)]
  | 87 => some [(1,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(0,3),(6,0)]
theorem root7Node43Domains0_fast_eq : root7Node43Domains0 = expandDomains root7Node43Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node43Domains0 v = expandDomains root7Node43Domains0Fast v from by decide) v
def root7Node43Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4)]
  | 1 => [(1,4)]
  | 2 => [(0,5)]
  | 3 => [(4,4)]
  | 4 => [(0,0)]
  | 5 => [(3,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(6,0)]
  | 9 => [(7,1)]
  | 10 => [(1,5)]
  | 11 => [(6,1)]
  | 12 => [(5,1)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(5,1)]
  | 22 => [(0,1)]
  | 23 => [(6,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(8,3)]
  | 31 => [(8,5)]
  | 32 => [(1,0)]
  | 33 => [(7,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(8,1)]
  | 37 => [(6,5)]
  | 38 => [(0,4)]
  | 39 => [(5,4)]
  | 40 => [(7,4)]
  | 41 => [(1,3)]
  | 42 => [(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(8,5)]
  | 48 => [(7,0)]
  | 49 => [(4,3)]
  | 50 => [(7,5)]
  | 51 => [(6,5)]
  | 52 => [(0,4)]
  | 53 => [(5,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(6,3)]
  | 58 => [(7,2)]
  | 59 => [(7,4)]
  | 60 => [(6,3)]
  | 61 => [(7,0)]
  | 62 => [(4,3)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(4,1)]
  | 66 => [(0,2)]
  | 67 => [(1,1)]
  | 68 => [(4,1)]
  | 69 => [(0,2)]
  | 70 => [(1,4)]
  | 71 => [(0,5)]
  | 72 => [(2,0)]
  | 73 => [(7,3)]
  | 74 => [(5,2)]
  | 75 => [(8,0)]
  | 76 => [(7,3)]
  | 77 => [(5,2)]
  | 78 => [(6,0)]
  | 79 => [(3,1)]
  | 80 => [(0,1)]
  | 81 => [(6,2)]
  | 82 => [(8,4)]
  | 83 => [(6,4)]
  | 84 => [(1,2)]
  | 85 => [(5,0)]
  | 86 => [(4,5)]
  | 87 => [(1,0)]
  | 88 => [(7,1)]
  | 89 => [(7,5)]
  | _ => [(0,3)]
def root7Node43Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(1,4)]
  | 2 => some [(0,5)]
  | 3 => some [(4,4)]
  | 4 => some [(0,0)]
  | 5 => some [(3,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(6,0)]
  | 9 => some [(7,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(5,1)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,3)]
  | 31 => some [(8,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(5,4)]
  | 40 => some [(7,4)]
  | 41 => some [(1,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(7,0)]
  | 49 => some [(4,3)]
  | 50 => some [(7,5)]
  | 51 => some [(6,5)]
  | 52 => some [(0,4)]
  | 53 => some [(5,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(6,3)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | 60 => some [(6,3)]
  | 61 => some [(7,0)]
  | 62 => some [(4,3)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(4,1)]
  | 66 => some [(0,2)]
  | 67 => some [(1,1)]
  | 68 => some [(4,1)]
  | 69 => some [(0,2)]
  | 70 => some [(1,4)]
  | 71 => some [(0,5)]
  | 72 => some [(2,0)]
  | 73 => some [(7,3)]
  | 74 => some [(5,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(5,2)]
  | 78 => some [(6,0)]
  | 79 => some [(3,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(5,0)]
  | 86 => some [(4,5)]
  | 87 => some [(1,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(0,3)]
theorem root7Node43Domains1_fast_eq : root7Node43Domains1 = expandDomains root7Node43Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node43Domains1 v = expandDomains root7Node43Domains1Fast v from by decide) v
theorem root7Node43Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Narrowing_checked :
    checkNarrowing table56 root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root7Node43Domains0 root7Node43Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node43Step1Chunk0_0_checked, root7Node43Step1Chunk0_1_checked, root7Node43Step1Chunk0_2_checked, root7Node43Step1Chunk0_3_checked, root7Node43Step1Chunk0_4_checked, root7Node43Step1Chunk0_5_checked, root7Node43Step1Chunk1_0_checked, root7Node43Step1Chunk1_1_checked, root7Node43Step1Chunk1_2_checked, root7Node43Step1Chunk1_3_checked, root7Node43Step1Chunk1_4_checked, root7Node43Step1Chunk1_5_checked, root7Node43Step1Chunk2_0_checked, root7Node43Step1Chunk2_1_checked, root7Node43Step1Chunk2_2_checked, root7Node43Step1Chunk2_3_checked, root7Node43Step1Chunk2_4_checked, root7Node43Step1Chunk2_5_checked, root7Node43Step1Chunk3_0_checked, root7Node43Step1Chunk3_1_checked, root7Node43Step1Chunk3_2_checked, root7Node43Step1Chunk3_3_checked, root7Node43Step1Chunk3_4_checked, root7Node43Step1Chunk3_5_checked, root7Node43Step1Chunk4_0_checked, root7Node43Step1Chunk4_1_checked, root7Node43Step1Chunk4_2_checked, root7Node43Step1Chunk4_3_checked, root7Node43Step1Chunk4_4_checked, root7Node43Step1Chunk4_5_checked, root7Node43Step1Chunk5_0_checked, root7Node43Step1Chunk5_1_checked, root7Node43Step1Chunk5_2_checked, root7Node43Step1Chunk5_3_checked, root7Node43Step1Chunk5_4_checked, root7Node43Step1Chunk5_5_checked, root7Node43Step1Chunk6_0_checked, root7Node43Step1Chunk6_1_checked, root7Node43Step1Chunk6_2_checked, root7Node43Step1Chunk6_3_checked, root7Node43Step1Chunk6_4_checked, root7Node43Step1Chunk6_5_checked, root7Node43Step1Chunk7_0_checked, root7Node43Step1Chunk7_1_checked, root7Node43Step1Chunk7_2_checked, root7Node43Step1Chunk7_3_checked, root7Node43Step1Chunk7_4_checked, root7Node43Step1Chunk7_5_checked, root7Node43Step1Chunk8_0_checked, root7Node43Step1Chunk8_1_checked, root7Node43Step1Chunk8_2_checked, root7Node43Step1Chunk8_3_checked, root7Node43Step1Chunk8_4_checked, root7Node43Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node43Step1_checked :
    checkReplacement table56 root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq
    root7Node43Step1Narrowing_checked (by decide)
theorem root7Node43Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node43Domains1 (.output 19) = true := by decide
def root7Node44Domains0 : Domains 91 State := restrict root7Node40Domains4 5 (7,2)
def root7Node44Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(1,4)]
  | 2 => some [(0,5)]
  | 3 => some [(4,4)]
  | 4 => some [(0,0)]
  | 5 => some [(7,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(6,0)]
  | 9 => some [(7,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(5,1)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,3)]
  | 31 => some [(8,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(5,4)]
  | 40 => some [(7,4)]
  | 41 => some [(1,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(7,0)]
  | 49 => some [(4,3)]
  | 50 => some [(7,5)]
  | 51 => some [(6,5)]
  | 52 => some [(0,4)]
  | 53 => some [(5,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(6,3)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | 60 => some [(1,3),(6,3)]
  | 61 => some [(7,0)]
  | 62 => some [(4,3)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(4,1)]
  | 66 => some [(0,2)]
  | 67 => some [(1,1)]
  | 68 => some [(4,1),(8,1)]
  | 69 => some [(0,2),(6,5)]
  | 70 => some [(1,4)]
  | 71 => some [(0,5)]
  | 72 => some [(2,0)]
  | 73 => some [(7,3)]
  | 74 => some [(5,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3),(8,3)]
  | 77 => some [(5,2),(5,5)]
  | 78 => some [(6,0)]
  | 79 => some [(3,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(1,4),(6,4)]
  | 84 => some [(0,5),(1,2)]
  | 85 => some [(5,0)]
  | 86 => some [(4,5)]
  | 87 => some [(1,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(0,3),(6,0)]
theorem root7Node44Domains0_fast_eq : root7Node44Domains0 = expandDomains root7Node44Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node44Domains0 v = expandDomains root7Node44Domains0Fast v from by decide) v
def root7Node44Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4)]
  | 1 => [(1,4)]
  | 2 => [(0,5)]
  | 3 => [(4,4)]
  | 4 => [(0,0)]
  | 5 => [(7,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(6,0)]
  | 9 => [(7,1)]
  | 10 => [(1,5)]
  | 11 => [(6,1)]
  | 12 => [(5,1)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(5,1)]
  | 22 => [(0,1)]
  | 23 => [(6,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(8,3)]
  | 31 => [(8,5)]
  | 32 => [(1,0)]
  | 33 => [(7,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(8,1)]
  | 37 => [(6,5)]
  | 38 => [(0,4)]
  | 39 => [(5,4)]
  | 40 => [(7,4)]
  | 41 => [(1,3)]
  | 42 => [(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(8,5)]
  | 48 => [(7,0)]
  | 49 => [(4,3)]
  | 50 => [(7,5)]
  | 51 => [(6,5)]
  | 52 => [(0,4)]
  | 53 => [(5,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(6,3)]
  | 58 => [(7,2)]
  | 59 => [(7,4)]
  | 60 => [(6,3)]
  | 61 => [(7,0)]
  | 62 => [(4,3)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(4,1)]
  | 66 => [(0,2)]
  | 67 => [(1,1)]
  | 68 => [(4,1)]
  | 69 => [(0,2)]
  | 70 => [(1,4)]
  | 71 => [(0,5)]
  | 72 => [(2,0)]
  | 73 => [(7,3)]
  | 74 => [(5,2)]
  | 75 => [(8,0)]
  | 76 => [(7,3)]
  | 77 => [(5,2)]
  | 78 => [(6,0)]
  | 79 => [(3,1)]
  | 80 => [(0,1)]
  | 81 => [(6,2)]
  | 82 => [(8,4)]
  | 83 => [(1,4),(6,4)]
  | 84 => [(0,5),(1,2)]
  | 85 => [(5,0)]
  | 86 => [(4,5)]
  | 87 => [(1,0)]
  | 88 => [(7,1)]
  | 89 => [(7,5)]
  | _ => [(0,3),(6,0)]
def root7Node44Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4)]
  | 1 => some [(1,4)]
  | 2 => some [(0,5)]
  | 3 => some [(4,4)]
  | 4 => some [(0,0)]
  | 5 => some [(7,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(6,0)]
  | 9 => some [(7,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(5,1)]
  | 22 => some [(0,1)]
  | 23 => some [(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,3)]
  | 31 => some [(8,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(5,4)]
  | 40 => some [(7,4)]
  | 41 => some [(1,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(7,0)]
  | 49 => some [(4,3)]
  | 50 => some [(7,5)]
  | 51 => some [(6,5)]
  | 52 => some [(0,4)]
  | 53 => some [(5,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(6,3)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | 60 => some [(6,3)]
  | 61 => some [(7,0)]
  | 62 => some [(4,3)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(4,1)]
  | 66 => some [(0,2)]
  | 67 => some [(1,1)]
  | 68 => some [(4,1)]
  | 69 => some [(0,2)]
  | 70 => some [(1,4)]
  | 71 => some [(0,5)]
  | 72 => some [(2,0)]
  | 73 => some [(7,3)]
  | 74 => some [(5,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(5,2)]
  | 78 => some [(6,0)]
  | 79 => some [(3,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(1,4),(6,4)]
  | 84 => some [(0,5),(1,2)]
  | 85 => some [(5,0)]
  | 86 => some [(4,5)]
  | 87 => some [(1,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(0,3),(6,0)]
theorem root7Node44Domains1_fast_eq : root7Node44Domains1 = expandDomains root7Node44Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node44Domains1 v = expandDomains root7Node44Domains1Fast v from by decide) v
theorem root7Node44Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq (by decide)
theorem root7Node44Step1Narrowing_checked :
    checkNarrowing table36 root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root7Node44Domains0 root7Node44Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node44Step1Chunk0_0_checked, root7Node44Step1Chunk0_1_checked, root7Node44Step1Chunk0_2_checked, root7Node44Step1Chunk0_3_checked, root7Node44Step1Chunk0_4_checked, root7Node44Step1Chunk0_5_checked, root7Node44Step1Chunk1_0_checked, root7Node44Step1Chunk1_1_checked, root7Node44Step1Chunk1_2_checked, root7Node44Step1Chunk1_3_checked, root7Node44Step1Chunk1_4_checked, root7Node44Step1Chunk1_5_checked, root7Node44Step1Chunk2_0_checked, root7Node44Step1Chunk2_1_checked, root7Node44Step1Chunk2_2_checked, root7Node44Step1Chunk2_3_checked, root7Node44Step1Chunk2_4_checked, root7Node44Step1Chunk2_5_checked, root7Node44Step1Chunk3_0_checked, root7Node44Step1Chunk3_1_checked, root7Node44Step1Chunk3_2_checked, root7Node44Step1Chunk3_3_checked, root7Node44Step1Chunk3_4_checked, root7Node44Step1Chunk3_5_checked, root7Node44Step1Chunk4_0_checked, root7Node44Step1Chunk4_1_checked, root7Node44Step1Chunk4_2_checked, root7Node44Step1Chunk4_3_checked, root7Node44Step1Chunk4_4_checked, root7Node44Step1Chunk4_5_checked, root7Node44Step1Chunk5_0_checked, root7Node44Step1Chunk5_1_checked, root7Node44Step1Chunk5_2_checked, root7Node44Step1Chunk5_3_checked, root7Node44Step1Chunk5_4_checked, root7Node44Step1Chunk5_5_checked, root7Node44Step1Chunk6_0_checked, root7Node44Step1Chunk6_1_checked, root7Node44Step1Chunk6_2_checked, root7Node44Step1Chunk6_3_checked, root7Node44Step1Chunk6_4_checked, root7Node44Step1Chunk6_5_checked, root7Node44Step1Chunk7_0_checked, root7Node44Step1Chunk7_1_checked, root7Node44Step1Chunk7_2_checked, root7Node44Step1Chunk7_3_checked, root7Node44Step1Chunk7_4_checked, root7Node44Step1Chunk7_5_checked, root7Node44Step1Chunk8_0_checked, root7Node44Step1Chunk8_1_checked, root7Node44Step1Chunk8_2_checked, root7Node44Step1Chunk8_3_checked, root7Node44Step1Chunk8_4_checked, root7Node44Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node44Step1_checked :
    checkReplacement table36 root7Node44Domains0 root7Node44Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node44Domains0 root7Node44Domains1
    root7Node44Domains0Fast root7Node44Domains1Fast
    root7Node44Domains0_fast_eq root7Node44Domains1_fast_eq
    root7Node44Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
