module

public import SpectreFinite.RadiusFiveRoot8Part12
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable21
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node28Domains0 : Domains 91 State := restrict root8Node26Domains1 86 (7,5)
def root8Node28Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(3,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(2,2)]
  | 30 => some [(2,3)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,4)]
  | 41 => some [(1,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0)]
  | 51 => some [(0,3)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,3)]
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
  | 86 => some [(7,5)]
  | 87 => some [(0,3)]
  | 88 => some [(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root8Node28Domains0_fast_eq : root8Node28Domains0 = expandDomains root8Node28Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node28Domains0 v = expandDomains root8Node28Domains0Fast v from by decide) v
theorem root8Node28Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node28Domains0 (.output 12) = true := by decide
def root8Node29Domains0 : Domains 91 State := restrict root8Node25Domains1 70 (6,3)
def root8Node29Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(3,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(2,2)]
  | 30 => some [(2,3)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,4)]
  | 41 => some [(1,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0)]
  | 51 => some [(0,3)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
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
theorem root8Node29Domains0_fast_eq : root8Node29Domains0 = expandDomains root8Node29Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node29Domains0 v = expandDomains root8Node29Domains0Fast v from by decide) v
def root8Node29Domains1 (v : Fin 91) : List State :=
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
  | 14 => [(8,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(3,4)]
  | 22 => [(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => [(2,2)]
  | 30 => [(2,3)]
  | 31 => [(0,2)]
  | 32 => [(1,1)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(0,1)]
  | 40 => [(6,4)]
  | 41 => [(1,2)]
  | 42 => [(4,0)]
  | 43 => [(7,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(1,0)]
  | 51 => [(0,3)]
  | 52 => [(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(5,3)]
  | 62 => [(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(8,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
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
def root8Node29Domains1Fast (v : Fin 91) : Option (List State) :=
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
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(3,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(2,2)]
  | 30 => some [(2,3)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,4)]
  | 41 => some [(1,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0)]
  | 51 => some [(0,3)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
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
theorem root8Node29Domains1_fast_eq : root8Node29Domains1 = expandDomains root8Node29Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node29Domains1 v = expandDomains root8Node29Domains1Fast v from by decide) v
theorem root8Node29Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq (by decide)
theorem root8Node29Step1Narrowing_checked :
    checkNarrowing table54 root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root8Node29Domains0 root8Node29Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node29Step1Chunk0_0_checked, root8Node29Step1Chunk0_1_checked, root8Node29Step1Chunk0_2_checked, root8Node29Step1Chunk0_3_checked, root8Node29Step1Chunk0_4_checked, root8Node29Step1Chunk0_5_checked, root8Node29Step1Chunk1_0_checked, root8Node29Step1Chunk1_1_checked, root8Node29Step1Chunk1_2_checked, root8Node29Step1Chunk1_3_checked, root8Node29Step1Chunk1_4_checked, root8Node29Step1Chunk1_5_checked, root8Node29Step1Chunk2_0_checked, root8Node29Step1Chunk2_1_checked, root8Node29Step1Chunk2_2_checked, root8Node29Step1Chunk2_3_checked, root8Node29Step1Chunk2_4_checked, root8Node29Step1Chunk2_5_checked, root8Node29Step1Chunk3_0_checked, root8Node29Step1Chunk3_1_checked, root8Node29Step1Chunk3_2_checked, root8Node29Step1Chunk3_3_checked, root8Node29Step1Chunk3_4_checked, root8Node29Step1Chunk3_5_checked, root8Node29Step1Chunk4_0_checked, root8Node29Step1Chunk4_1_checked, root8Node29Step1Chunk4_2_checked, root8Node29Step1Chunk4_3_checked, root8Node29Step1Chunk4_4_checked, root8Node29Step1Chunk4_5_checked, root8Node29Step1Chunk5_0_checked, root8Node29Step1Chunk5_1_checked, root8Node29Step1Chunk5_2_checked, root8Node29Step1Chunk5_3_checked, root8Node29Step1Chunk5_4_checked, root8Node29Step1Chunk5_5_checked, root8Node29Step1Chunk6_0_checked, root8Node29Step1Chunk6_1_checked, root8Node29Step1Chunk6_2_checked, root8Node29Step1Chunk6_3_checked, root8Node29Step1Chunk6_4_checked, root8Node29Step1Chunk6_5_checked, root8Node29Step1Chunk7_0_checked, root8Node29Step1Chunk7_1_checked, root8Node29Step1Chunk7_2_checked, root8Node29Step1Chunk7_3_checked, root8Node29Step1Chunk7_4_checked, root8Node29Step1Chunk7_5_checked, root8Node29Step1Chunk8_0_checked, root8Node29Step1Chunk8_1_checked, root8Node29Step1Chunk8_2_checked, root8Node29Step1Chunk8_3_checked, root8Node29Step1Chunk8_4_checked, root8Node29Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node29Step1_checked :
    checkReplacement table54 root8Node29Domains0 root8Node29Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node29Domains0 root8Node29Domains1
    root8Node29Domains0Fast root8Node29Domains1Fast
    root8Node29Domains0_fast_eq root8Node29Domains1_fast_eq
    root8Node29Step1Narrowing_checked (by decide)
theorem root8Node29Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node29Domains1 (.output 13) = true := by decide
def root8Node30Domains0 : Domains 91 State := restrict root8Node22Domains3 21 (7,4)
def root8Node30Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3),(6,3)]
  | 29 => some [(2,2),(4,2)]
  | 30 => some [(2,1),(2,3)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1),(8,1)]
  | 37 => some [(0,2),(6,5)]
  | 38 => some [(0,4),(1,1)]
  | 39 => some [(0,1),(1,4)]
  | 40 => some [(0,0),(6,4)]
  | 41 => some [(1,2),(3,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3),(8,3)]
  | 47 => some [(5,2),(5,5)]
  | 48 => some [(3,0),(5,0)]
  | 49 => some [(2,5),(4,5)]
  | 50 => some [(1,0),(6,0)]
  | 51 => some [(0,3),(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(1,4),(6,4)]
  | 57 => some [(0,5),(1,2)]
  | 58 => some [(4,4),(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,3),(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3),(6,0)]
  | 67 => some [(7,1),(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(1,3),(6,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2),(8,2)]
  | 75 => some [(5,0),(5,3)]
  | 76 => some [(4,5),(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(1,1)]
  | 79 => some [(5,1),(5,4)]
  | 80 => some [(0,1),(6,4)]
  | 81 => some [(1,2),(6,2)]
  | 82 => some [(7,4),(8,4)]
  | 83 => some [(0,0),(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5),(7,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(2,1),(4,1),(8,1)]
  | 89 => some [(0,2),(1,5)]
  | _ => some [(1,1),(6,1)]
theorem root8Node30Domains0_fast_eq : root8Node30Domains0 = expandDomains root8Node30Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node30Domains0 v = expandDomains root8Node30Domains0Fast v from by decide) v
def root8Node30Domains1 (v : Fin 91) : List State :=
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
  | 14 => [(8,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(7,4)]
  | 22 => [(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3),(6,3)]
  | 29 => [(2,2),(4,2)]
  | 30 => [(2,1)]
  | 31 => [(0,2)]
  | 32 => [(1,1)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1),(8,1)]
  | 37 => [(0,2),(6,5)]
  | 38 => [(0,4),(1,1)]
  | 39 => [(0,1),(1,4)]
  | 40 => [(0,0)]
  | 41 => [(3,2)]
  | 42 => [(4,0)]
  | 43 => [(7,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3),(8,3)]
  | 47 => [(5,2),(5,5)]
  | 48 => [(3,0),(5,0)]
  | 49 => [(2,5),(4,5)]
  | 50 => [(1,0),(6,0)]
  | 51 => [(6,1)]
  | 52 => [(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(1,4),(6,4)]
  | 57 => [(0,5),(1,2)]
  | 58 => [(4,4),(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3),(6,0)]
  | 67 => [(7,1),(8,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(1,3),(6,3)]
  | 71 => [(7,2),(8,2)]
  | 72 => [(4,0),(8,0)]
  | 73 => [(7,3)]
  | 74 => [(4,2),(8,2)]
  | 75 => [(5,0),(5,3)]
  | 76 => [(4,5),(8,5)]
  | 77 => [(7,0)]
  | 78 => [(0,4),(1,1)]
  | 79 => [(5,1),(5,4)]
  | 80 => [(0,1),(6,4)]
  | 81 => [(1,2),(6,2)]
  | 82 => [(7,4),(8,4)]
  | 83 => [(0,0),(6,3)]
  | 84 => [(7,2)]
  | 85 => [(4,3),(8,3)]
  | 86 => [(3,5),(5,5),(7,5)]
  | 87 => [(0,3),(1,0)]
  | 88 => [(2,1),(4,1),(8,1)]
  | 89 => [(0,2),(1,5)]
  | _ => [(1,1),(6,1)]
def root8Node30Domains1Fast (v : Fin 91) : Option (List State) :=
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
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3),(6,3)]
  | 29 => some [(2,2),(4,2)]
  | 30 => some [(2,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1),(8,1)]
  | 37 => some [(0,2),(6,5)]
  | 38 => some [(0,4),(1,1)]
  | 39 => some [(0,1),(1,4)]
  | 40 => some [(0,0)]
  | 41 => some [(3,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3),(8,3)]
  | 47 => some [(5,2),(5,5)]
  | 48 => some [(3,0),(5,0)]
  | 49 => some [(2,5),(4,5)]
  | 50 => some [(1,0),(6,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(1,4),(6,4)]
  | 57 => some [(0,5),(1,2)]
  | 58 => some [(4,4),(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3),(6,0)]
  | 67 => some [(7,1),(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(1,3),(6,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2),(8,2)]
  | 75 => some [(5,0),(5,3)]
  | 76 => some [(4,5),(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(1,1)]
  | 79 => some [(5,1),(5,4)]
  | 80 => some [(0,1),(6,4)]
  | 81 => some [(1,2),(6,2)]
  | 82 => some [(7,4),(8,4)]
  | 83 => some [(0,0),(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5),(7,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(2,1),(4,1),(8,1)]
  | 89 => some [(0,2),(1,5)]
  | _ => some [(1,1),(6,1)]
theorem root8Node30Domains1_fast_eq : root8Node30Domains1 = expandDomains root8Node30Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node30Domains1 v = expandDomains root8Node30Domains1Fast v from by decide) v
theorem root8Node30Step1Chunk0_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_0⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk0_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_1⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk0_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_2⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk0_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_3⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk0_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_4⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk0_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_5⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk1_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_0⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk1_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_1⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk1_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_2⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk1_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_3⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk1_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_4⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk1_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_5⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk2_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_0⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk2_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_1⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk2_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_2⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk2_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_3⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk2_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_4⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk2_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_5⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk3_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_0⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk3_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_1⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk3_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_2⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk3_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_3⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk3_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_4⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk3_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_5⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk4_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_0⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk4_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_1⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk4_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_2⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk4_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_3⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk4_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_4⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk4_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_5⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk5_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_0⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk5_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_1⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk5_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_2⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk5_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_3⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk5_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_4⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk5_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_5⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk6_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_0⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk6_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_1⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk6_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_2⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk6_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_3⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk6_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_4⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk6_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_5⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk7_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_0⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk7_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_1⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk7_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_2⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk7_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_3⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk7_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_4⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk7_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_5⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk8_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_0⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk8_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_1⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk8_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_2⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk8_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_3⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk8_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_4⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Chunk8_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_5⟩
      root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq (by decide)
theorem root8Node30Step1Narrowing_checked :
    checkNarrowing table21 root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkNarrowing_flatten table21Scope [table21Rows0_0,table21Rows0_1,table21Rows0_2,table21Rows0_3,table21Rows0_4,table21Rows0_5,table21Rows1_0,table21Rows1_1,table21Rows1_2,table21Rows1_3,table21Rows1_4,table21Rows1_5,table21Rows2_0,table21Rows2_1,table21Rows2_2,table21Rows2_3,table21Rows2_4,table21Rows2_5,table21Rows3_0,table21Rows3_1,table21Rows3_2,table21Rows3_3,table21Rows3_4,table21Rows3_5,table21Rows4_0,table21Rows4_1,table21Rows4_2,table21Rows4_3,table21Rows4_4,table21Rows4_5,table21Rows5_0,table21Rows5_1,table21Rows5_2,table21Rows5_3,table21Rows5_4,table21Rows5_5,table21Rows6_0,table21Rows6_1,table21Rows6_2,table21Rows6_3,table21Rows6_4,table21Rows6_5,table21Rows7_0,table21Rows7_1,table21Rows7_2,table21Rows7_3,table21Rows7_4,table21Rows7_5,table21Rows8_0,table21Rows8_1,table21Rows8_2,table21Rows8_3,table21Rows8_4,table21Rows8_5]
    root8Node30Domains0 root8Node30Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node30Step1Chunk0_0_checked, root8Node30Step1Chunk0_1_checked, root8Node30Step1Chunk0_2_checked, root8Node30Step1Chunk0_3_checked, root8Node30Step1Chunk0_4_checked, root8Node30Step1Chunk0_5_checked, root8Node30Step1Chunk1_0_checked, root8Node30Step1Chunk1_1_checked, root8Node30Step1Chunk1_2_checked, root8Node30Step1Chunk1_3_checked, root8Node30Step1Chunk1_4_checked, root8Node30Step1Chunk1_5_checked, root8Node30Step1Chunk2_0_checked, root8Node30Step1Chunk2_1_checked, root8Node30Step1Chunk2_2_checked, root8Node30Step1Chunk2_3_checked, root8Node30Step1Chunk2_4_checked, root8Node30Step1Chunk2_5_checked, root8Node30Step1Chunk3_0_checked, root8Node30Step1Chunk3_1_checked, root8Node30Step1Chunk3_2_checked, root8Node30Step1Chunk3_3_checked, root8Node30Step1Chunk3_4_checked, root8Node30Step1Chunk3_5_checked, root8Node30Step1Chunk4_0_checked, root8Node30Step1Chunk4_1_checked, root8Node30Step1Chunk4_2_checked, root8Node30Step1Chunk4_3_checked, root8Node30Step1Chunk4_4_checked, root8Node30Step1Chunk4_5_checked, root8Node30Step1Chunk5_0_checked, root8Node30Step1Chunk5_1_checked, root8Node30Step1Chunk5_2_checked, root8Node30Step1Chunk5_3_checked, root8Node30Step1Chunk5_4_checked, root8Node30Step1Chunk5_5_checked, root8Node30Step1Chunk6_0_checked, root8Node30Step1Chunk6_1_checked, root8Node30Step1Chunk6_2_checked, root8Node30Step1Chunk6_3_checked, root8Node30Step1Chunk6_4_checked, root8Node30Step1Chunk6_5_checked, root8Node30Step1Chunk7_0_checked, root8Node30Step1Chunk7_1_checked, root8Node30Step1Chunk7_2_checked, root8Node30Step1Chunk7_3_checked, root8Node30Step1Chunk7_4_checked, root8Node30Step1Chunk7_5_checked, root8Node30Step1Chunk8_0_checked, root8Node30Step1Chunk8_1_checked, root8Node30Step1Chunk8_2_checked, root8Node30Step1Chunk8_3_checked, root8Node30Step1Chunk8_4_checked, root8Node30Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node30Step1_checked :
    checkReplacement table21 root8Node30Domains0 root8Node30Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node30Domains0 root8Node30Domains1
    root8Node30Domains0Fast root8Node30Domains1Fast
    root8Node30Domains0_fast_eq root8Node30Domains1_fast_eq
    root8Node30Step1Narrowing_checked (by decide)
def root8Node31Domains0 : Domains 91 State := restrict root8Node30Domains1 28 (1,3)
def root8Node31Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(2,2),(4,2)]
  | 30 => some [(2,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1),(8,1)]
  | 37 => some [(0,2),(6,5)]
  | 38 => some [(0,4),(1,1)]
  | 39 => some [(0,1),(1,4)]
  | 40 => some [(0,0)]
  | 41 => some [(3,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3),(8,3)]
  | 47 => some [(5,2),(5,5)]
  | 48 => some [(3,0),(5,0)]
  | 49 => some [(2,5),(4,5)]
  | 50 => some [(1,0),(6,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(1,4),(6,4)]
  | 57 => some [(0,5),(1,2)]
  | 58 => some [(4,4),(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3),(6,0)]
  | 67 => some [(7,1),(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(1,3),(6,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2),(8,2)]
  | 75 => some [(5,0),(5,3)]
  | 76 => some [(4,5),(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(1,1)]
  | 79 => some [(5,1),(5,4)]
  | 80 => some [(0,1),(6,4)]
  | 81 => some [(1,2),(6,2)]
  | 82 => some [(7,4),(8,4)]
  | 83 => some [(0,0),(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5),(7,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(2,1),(4,1),(8,1)]
  | 89 => some [(0,2),(1,5)]
  | _ => some [(1,1),(6,1)]
theorem root8Node31Domains0_fast_eq : root8Node31Domains0 = expandDomains root8Node31Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node31Domains0 v = expandDomains root8Node31Domains0Fast v from by decide) v
def root8Node31Domains1 (v : Fin 91) : List State :=
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
  | 14 => [(8,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(7,4)]
  | 22 => [(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(2,2),(4,2)]
  | 30 => [(2,1)]
  | 31 => [(0,2)]
  | 32 => [(1,1)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(8,1)]
  | 37 => [(6,5)]
  | 38 => [(0,4)]
  | 39 => [(0,1),(1,4)]
  | 40 => [(0,0)]
  | 41 => [(3,2)]
  | 42 => [(4,0)]
  | 43 => [(7,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(8,3)]
  | 47 => [(5,5)]
  | 48 => [(3,0)]
  | 49 => [(2,5)]
  | 50 => [(1,0),(6,0)]
  | 51 => [(6,1)]
  | 52 => [(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(1,4)]
  | 57 => [(0,5)]
  | 58 => [(4,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(6,0)]
  | 67 => [(7,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(1,3),(6,3)]
  | 71 => [(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3)]
  | 74 => [(8,2)]
  | 75 => [(5,0)]
  | 76 => [(4,5)]
  | 77 => [(7,0)]
  | 78 => [(0,4),(1,1)]
  | 79 => [(5,4)]
  | 80 => [(6,4)]
  | 81 => [(1,2)]
  | 82 => [(8,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(4,3),(8,3)]
  | 86 => [(7,5)]
  | 87 => [(0,3)]
  | 88 => [(8,1)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root8Node31Domains1Fast (v : Fin 91) : Option (List State) :=
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
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(2,2),(4,2)]
  | 30 => some [(2,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(0,1),(1,4)]
  | 40 => some [(0,0)]
  | 41 => some [(3,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5)]
  | 48 => some [(3,0)]
  | 49 => some [(2,5)]
  | 50 => some [(1,0),(6,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(1,3),(6,3)]
  | 71 => some [(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(5,0)]
  | 76 => some [(4,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(1,1)]
  | 79 => some [(5,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(8,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3)]
  | 88 => some [(8,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root8Node31Domains1_fast_eq : root8Node31Domains1 = expandDomains root8Node31Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node31Domains1 v = expandDomains root8Node31Domains1Fast v from by decide) v
theorem root8Node31Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq (by decide)
theorem root8Node31Step1Narrowing_checked :
    checkNarrowing table56 root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root8Node31Domains0 root8Node31Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node31Step1Chunk0_0_checked, root8Node31Step1Chunk0_1_checked, root8Node31Step1Chunk0_2_checked, root8Node31Step1Chunk0_3_checked, root8Node31Step1Chunk0_4_checked, root8Node31Step1Chunk0_5_checked, root8Node31Step1Chunk1_0_checked, root8Node31Step1Chunk1_1_checked, root8Node31Step1Chunk1_2_checked, root8Node31Step1Chunk1_3_checked, root8Node31Step1Chunk1_4_checked, root8Node31Step1Chunk1_5_checked, root8Node31Step1Chunk2_0_checked, root8Node31Step1Chunk2_1_checked, root8Node31Step1Chunk2_2_checked, root8Node31Step1Chunk2_3_checked, root8Node31Step1Chunk2_4_checked, root8Node31Step1Chunk2_5_checked, root8Node31Step1Chunk3_0_checked, root8Node31Step1Chunk3_1_checked, root8Node31Step1Chunk3_2_checked, root8Node31Step1Chunk3_3_checked, root8Node31Step1Chunk3_4_checked, root8Node31Step1Chunk3_5_checked, root8Node31Step1Chunk4_0_checked, root8Node31Step1Chunk4_1_checked, root8Node31Step1Chunk4_2_checked, root8Node31Step1Chunk4_3_checked, root8Node31Step1Chunk4_4_checked, root8Node31Step1Chunk4_5_checked, root8Node31Step1Chunk5_0_checked, root8Node31Step1Chunk5_1_checked, root8Node31Step1Chunk5_2_checked, root8Node31Step1Chunk5_3_checked, root8Node31Step1Chunk5_4_checked, root8Node31Step1Chunk5_5_checked, root8Node31Step1Chunk6_0_checked, root8Node31Step1Chunk6_1_checked, root8Node31Step1Chunk6_2_checked, root8Node31Step1Chunk6_3_checked, root8Node31Step1Chunk6_4_checked, root8Node31Step1Chunk6_5_checked, root8Node31Step1Chunk7_0_checked, root8Node31Step1Chunk7_1_checked, root8Node31Step1Chunk7_2_checked, root8Node31Step1Chunk7_3_checked, root8Node31Step1Chunk7_4_checked, root8Node31Step1Chunk7_5_checked, root8Node31Step1Chunk8_0_checked, root8Node31Step1Chunk8_1_checked, root8Node31Step1Chunk8_2_checked, root8Node31Step1Chunk8_3_checked, root8Node31Step1Chunk8_4_checked, root8Node31Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node31Step1_checked :
    checkReplacement table56 root8Node31Domains0 root8Node31Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node31Domains0 root8Node31Domains1
    root8Node31Domains0Fast root8Node31Domains1Fast
    root8Node31Domains0_fast_eq root8Node31Domains1_fast_eq
    root8Node31Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
